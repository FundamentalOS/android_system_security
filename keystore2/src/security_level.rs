// Copyright 2020, The Android Open Source Project
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This crate implements the IKeystoreSecurityLevel interface.

use crate::attestation_key_utils::{get_attest_key_info, AttestationKeyInfo};
use crate::audit_log::{
    log_key_deleted, log_key_generated, log_key_imported, log_key_integrity_violation,
};
use crate::database::{BlobInfo, CertificateInfo, KeyIdGuard};
use crate::error::{
    self, into_logged_binder, map_binder_status, map_binder_status_code, map_km_error,
    wrapped_rkpd_error_to_ks_error, Error, ErrorCode,
};
use android_security_compat::aidl::android::security::compat::IKeystoreCompatService::IKeystoreCompatService;
use crate::globals::{
    get_remotely_provisioned_component_name, DB, ENFORCEMENTS, LEGACY_IMPORTER, SUPER_KEY,
};
use crate::key_parameter::KeyParameterValue as KsKeyParamValue;
use crate::key_parameter::{KeyParameter as KsKeyParam, KmKeyParameter};
use crate::ks_err;
use crate::metrics_store::{
    log_key_creation_event_stats, log_operation_latency, parse_key_parameters,
};
use crate::remote_provisioning::RemProvState;
use crate::security_level_manager;
use crate::super_key::{KeyBlob, SuperKeyManager};
use crate::utils::{
    app_info_for_uid, check_device_attestation_permissions, check_key_permission,
    check_unique_id_attestation_permissions, count_key_entries, is_device_id_attestation_tag,
    key_characteristics_to_internal, log_security_safe_params, watchdog as wd, AndroidUserId,
    AppUid, Challenge, UNDEFINED_NOT_AFTER,
};
use crate::{
    database::{
        BlobMetaData, BlobMetaEntry, DateTime, KeyEntry, KeyEntryLoadBits, KeyMetaData,
        KeyMetaEntry, KeyType, SubComponentType, Uuid,
    },
    operation::KeystoreOperation,
    operation::LoggingInfo,
    operation::OperationDb,
    permission::KeyPerm,
};
use crate::{globals::get_keymint_device, id_rotation::IdRotationState};
use android_hardware_security_keymint::aidl::android::hardware::security::keymint::{
    Algorithm::Algorithm, AttestationKey::AttestationKey, Certificate::Certificate,
    HardwareAuthenticatorType::HardwareAuthenticatorType, IKeyMintDevice::IKeyMintDevice,
    KeyCreationResult::KeyCreationResult, KeyFormat::KeyFormat,
    KeyMintHardwareInfo::KeyMintHardwareInfo, KeyOrigin::KeyOrigin, KeyParameter::KeyParameter,
    KeyParameterValue::KeyParameterValue, SecurityLevel::SecurityLevel, Tag::Tag,
};
use android_hardware_security_keymint::binder::{BinderFeatures, Strong, ThreadState};
use android_security_metrics::aidl::android::security::metrics::OperationType::OperationType;
use android_system_keystore2::aidl::android::system::keystore2::{
    AuthenticatorSpec::AuthenticatorSpec, CreateOperationResponse::CreateOperationResponse,
    Domain::Domain, EphemeralStorageKeyResponse::EphemeralStorageKeyResponse,
    IKeystoreOperation::IKeystoreOperation, IKeystoreSecurityLevel::BnKeystoreSecurityLevel,
    IKeystoreSecurityLevel::IKeystoreSecurityLevel, KeyDescriptor::KeyDescriptor,
    KeyMetadata::KeyMetadata, KeyParameters::KeyParameters, ResponseCode::ResponseCode,
};
use anyhow::{anyhow, Context, Result};
use log::error;
use postprocessor_client::process_certificate_chain;
use rkpd_client::store_rkpd_attestation_key;
use rustutils::android::system_properties::read_bool;
use std::convert::TryInto;
use std::time::SystemTime;

/// The fallback limit on the number of keys per app.  All apps must stay within this limit.
const DEFAULT_PER_UID_KEY_LIMIT: i32 = 200_000;

/// The limit on the number of keys per app for apps with a target SDK level of 37+.
const API_37_PER_UID_KEY_LIMIT: i32 = 50_000;

/// Implementation of the IKeystoreSecurityLevel Interface.
pub struct KeystoreSecurityLevel {
    security_level: SecurityLevel,
    keymint: Strong<dyn IKeyMintDevice>,
    hw_info: KeyMintHardwareInfo,
    km_uuid: Uuid,
    operation_db: OperationDb,
    rem_prov_state: RemProvState,
    id_rotation_state: IdRotationState,
}

// Blob of 32 zeroes used as empty masking key.
static ZERO_BLOB_32: &[u8] = &[0; 32];

impl KeystoreSecurityLevel {
    /// Creates a new security level instance wrapped in a
    /// BnKeystoreSecurityLevel proxy object. It also enables
    /// `BinderFeatures::set_requesting_sid` on the new interface, because
    /// we need it for checking keystore permissions.
    pub fn new_native_binder(
        security_level: SecurityLevel,
        id_rotation_state: IdRotationState,
    ) -> Result<(Strong<dyn IKeystoreSecurityLevel>, Uuid)> {
        let (dev, hw_info, km_uuid) = get_keymint_device(&security_level)
            .context(ks_err!("KeystoreSecurityLevel::new_native_binder."))?;
        let result = BnKeystoreSecurityLevel::new_binder(
            Self {
                security_level,
                keymint: dev,
                hw_info,
                km_uuid,
                operation_db: OperationDb::new(),
                rem_prov_state: RemProvState::new(security_level),
                id_rotation_state,
            },
            BinderFeatures { set_requesting_sid: true, ..BinderFeatures::default() },
        );
        Ok((result, km_uuid))
    }

    fn watch_millis(&self, id: &'static str, millis: u64) -> Option<wd::WatchPoint> {
        let sec_level = self.security_level;
        wd::watch_millis_with(id, millis, sec_level)
    }

    fn watch(&self, id: &'static str) -> Option<wd::WatchPoint> {
        let sec_level = self.security_level;
        wd::watch_millis_with(id, wd::DEFAULT_TIMEOUT_MS, sec_level)
    }

    fn store_new_key(
        &self,
        key: KeyDescriptor,
        creation_result: KeyCreationResult,
        user: AndroidUserId,
        flags: Option<i32>,
    ) -> Result<KeyMetadata> {
        let KeyCreationResult {
            keyBlob: key_blob,
            keyCharacteristics: key_characteristics,
            certificateChain: mut certificate_chain,
        } = creation_result;

        // Unify the possible contents of the certificate chain.  The first entry in the `Vec` is
        // always the leaf certificate (if present), but the rest of the chain may be present as
        // either:
        //  - `certificate_chain[1..n]`: each entry holds a single certificate, as returned by
        //    KeyMint, or
        //  - `certificate[1`]: a single `Certificate` from RKP that actually (and confusingly)
        //    holds the DER-encoded certs of the chain concatenated together.
        let mut cert_info: CertificateInfo = CertificateInfo::new(
            // Leaf is always a single cert in the first entry, if present.
            match certificate_chain.len() {
                0 => None,
                _ => Some(certificate_chain.remove(0).encodedCertificate),
            },
            // Remainder may be either `[1..n]` individual certs, or just `[1]` holding a
            // concatenated chain. Convert the former to the latter.
            match certificate_chain.len() {
                0 => None,
                _ => Some(
                    certificate_chain
                        .iter()
                        .flat_map(|c| c.encodedCertificate.iter())
                        .copied()
                        .collect(),
                ),
            },
        );

        let mut key_parameters = key_characteristics_to_internal(key_characteristics);

        key_parameters
            .push(KsKeyParam::new(KsKeyParamValue::UserID(user.0), SecurityLevel::SOFTWARE));

        let creation_date = DateTime::now().context(ks_err!("Trying to make creation time."))?;

        let key = match key.domain {
            Domain::BLOB => KeyDescriptor {
                domain: Domain::BLOB,
                blob: Some(key_blob.to_vec()),
                ..Default::default()
            },
            _ => DB
                .with::<_, Result<KeyDescriptor>>(|db| {
                    let mut db = db.borrow_mut();

                    let (key_blob, mut blob_metadata) = SUPER_KEY
                        .read()
                        .unwrap()
                        .handle_super_encryption_on_key_init(
                            &mut db,
                            &LEGACY_IMPORTER,
                            &(key.domain),
                            &key_parameters,
                            flags,
                            user,
                            &key_blob,
                        )
                        .context(ks_err!("Failed to handle super encryption."))?;

                    let mut key_metadata = KeyMetaData::new();
                    key_metadata.add(KeyMetaEntry::CreationDate(creation_date));
                    blob_metadata.add(BlobMetaEntry::KmUuid(self.km_uuid));

                    let key_id = db
                        .store_new_key(
                            &key,
                            KeyType::Client,
                            &key_parameters,
                            &BlobInfo::new(&key_blob, &blob_metadata),
                            &cert_info,
                            &key_metadata,
                            &self.km_uuid,
                        )
                        .context(ks_err!())?;
                    Ok(KeyDescriptor {
                        domain: Domain::KEY_ID,
                        nspace: key_id.id(),
                        ..Default::default()
                    })
                })
                .context(ks_err!())?,
        };

        Ok(KeyMetadata {
            key,
            keySecurityLevel: self.security_level,
            certificate: cert_info.take_cert(),
            certificateChain: cert_info.take_cert_chain(),
            authorizations: crate::utils::key_parameters_to_authorizations(key_parameters),
            modificationTimeMs: creation_date.to_millis_epoch(),
        })
    }

    /// FundamentalOS: forge a software-backed key + keybox-signed attestation for a device-ID
    /// attestation request (mirrors TrickyStoreOSS CertificateGen.generateKeyPair). The key is
    /// generated on the software KeyMint so subsequent operations (sign) run in software; the
    /// attestation extension is forged to claim this security level with deviceLocked/Verified.
    #[allow(dead_code)]
    fn forge_software_key(
        &self,
        params: &[KeyParameter],
        ctx: &crate::attest_spoof::SpoofCtx,
        uid: u32,
    ) -> Result<KeyCreationResult> {
        // keymint_service_name() errors for SOFTWARE, so get_keymint_device(SOFTWARE) never reaches
        // the compat fallback. Go straight to the km_compat software KeyMint here.
        keystore2_km_compat::add_keymint_device_service();
        let compat: Strong<dyn IKeystoreCompatService> =
            map_binder_status_code(binder::get_interface("android.security.compat"))
                .context(ks_err!("Connecting to compat service for software forge."))?;
        let sw_km = map_binder_status(compat.getKeyMintDevice(SecurityLevel::SOFTWARE))
            .context(ks_err!("Getting software KeyMint from compat service."))?;
        let sw_params = crate::attest_spoof::software_keygen_params(params);
        let mut result = map_km_error({
            let _wp =
                self.watch("KeystoreSecurityLevel::forge_software_key: calling software generateKey");
            sw_km.generateKey(&sw_params, None)
        })
        .context(ks_err!("Software KeyMint generateKey failed."))?;
        let sw_leaf = result
            .certificateChain
            .first()
            .ok_or_else(Error::sys)
            .context(ks_err!("Software key produced no certificate."))?
            .encodedCertificate
            .clone();
        let forged =
            // Forge at the requested security level (matches what TrickyStoreOSS produces when it
            // intercepts the same request — DroidGuard requests TEE for its attestation key).
            crate::attest_spoof::forge_cert(&sw_leaf, ctx, self.security_level.0 as i64, uid)
                .ok_or_else(Error::sys)
                .context(ks_err!("forge_cert failed."))?;
        result.certificateChain =
            forged.into_iter().map(|der| Certificate { encodedCertificate: der }).collect();
        crate::attest_spoof::patch_forge_characteristics(&mut result, ctx, self.security_level);
        Ok(result)
    }

    fn create_operation(
        &self,
        key: &KeyDescriptor,
        operation_parameters: &[KeyParameter],
        forced: bool,
    ) -> Result<CreateOperationResponse> {
        let caller_uid = AppUid::calling();
        // We use `scoping_blob` to extend the life cycle of the blob loaded from the database,
        // so that we can use it by reference like the blob provided by the key descriptor.
        // Otherwise, we would have to clone the blob from the key descriptor.
        let scoping_blob: Vec<u8>;
        let mut is_attested = false;
        let (km_blob, key_properties, key_id_guard, blob_metadata) = match key.domain {
            Domain::BLOB => {
                check_key_permission(KeyPerm::Use, key, &None)
                    .context(ks_err!("checking use permission for Domain::BLOB."))?;
                if forced {
                    check_key_permission(KeyPerm::ReqForcedOp, key, &None)
                        .context(ks_err!("checking forced permission for Domain::BLOB."))?;
                }
                (
                    match &key.blob {
                        Some(blob) => blob,
                        None => {
                            return Err(Error::sys()).context(ks_err!(
                                "Key blob must be specified when \
                                using Domain::BLOB."
                            ));
                        }
                    },
                    None,
                    None,
                    BlobMetaData::new(),
                )
            }
            _ => {
                let super_key = SUPER_KEY
                    .read()
                    .unwrap()
                    .get_credential_encrypted_key_by_user_id(caller_uid.owning_user());
                let (key_id_guard, mut key_entry) = DB
                    .with::<_, Result<(KeyIdGuard, KeyEntry)>>(|db| {
                        LEGACY_IMPORTER.with_try_import(key, caller_uid, super_key, || {
                            db.borrow_mut().load_key_entry(
                                key,
                                KeyType::Client,
                                KeyEntryLoadBits::BOTH,
                                caller_uid,
                                |k, av| {
                                    check_key_permission(KeyPerm::Use, k, &av)?;
                                    if forced {
                                        check_key_permission(KeyPerm::ReqForcedOp, k, &av)?;
                                    }
                                    Ok(())
                                },
                            )
                        })
                    })
                    .context(ks_err!("Failed to load key blob."))?;

                is_attested = key_entry.is_attested();

                let (blob, blob_metadata) =
                    key_entry.take_key_blob_info().ok_or_else(Error::sys).context(ks_err!(
                        "Successfully loaded key entry, \
                        but KM blob was missing."
                    ))?;
                scoping_blob = blob;

                (
                    &scoping_blob,
                    Some((key_id_guard.id(), key_entry.into_key_parameters())),
                    Some(key_id_guard),
                    blob_metadata,
                )
            }
        };

        let purpose = operation_parameters.iter().find(|p| p.tag == Tag::PURPOSE).map_or(
            Err(Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("No operation purpose specified.")),
            |kp| match kp.value {
                KeyParameterValue::KeyPurpose(p) => Ok(p),
                _ => Err(Error::Km(ErrorCode::INVALID_ARGUMENT))
                    .context(ks_err!("Malformed KeyParameter.")),
            },
        )?;

        // Remove Tag::PURPOSE from the operation_parameters, since some keymaster devices return
        // an error on begin() if Tag::PURPOSE is in the operation_parameters.
        let op_params: Vec<KeyParameter> =
            operation_parameters.iter().filter(|p| p.tag != Tag::PURPOSE).cloned().collect();
        let operation_parameters = op_params.as_slice();

        let (immediate_hat, mut auth_info) = ENFORCEMENTS
            .authorize_create(
                purpose,
                key_properties.as_ref(),
                operation_parameters.as_ref(),
                self.hw_info.timestampTokenRequired,
            )
            .context(ks_err!())?;

        let km_blob = SUPER_KEY
            .read()
            .unwrap()
            .unwrap_key_if_required(&blob_metadata, km_blob)
            .context(ks_err!("Failed to handle super encryption."))?;

        let (begin_result, upgraded_blob) = self
            .upgrade_keyblob_if_required_with(
                key_id_guard,
                &km_blob,
                blob_metadata.km_uuid().copied(),
                operation_parameters,
                |blob| loop {
                    match map_km_error({
                        let _wp = self.watch(
                            "KeystoreSecurityLevel::create_operation: calling IKeyMintDevice::begin",
                        );
                        self.keymint.begin(
                            purpose,
                            blob,
                            operation_parameters,
                            immediate_hat.as_ref(),
                        )
                    }) {
                        Err(Error::Km(ErrorCode::TOO_MANY_OPERATIONS)) => {
                            self.operation_db.prune(caller_uid, forced)?;
                            continue;
                        }
                        v @ Err(Error::Km(ErrorCode::INVALID_KEY_BLOB)) => {
                            if let Some((key_id, _)) = key_properties {
                                if let Ok(Some(key)) =
                                    DB.with(|db| db.borrow_mut().load_key_descriptor(key_id))
                                {
                                    log_key_integrity_violation(&key);
                                } else {
                                    error!("Failed to load key descriptor for audit log");
                                }
                            }
                            return v;
                        }
                        v => return v,
                    }
                },
            )
            .context(ks_err!("Failed to begin operation."))?;

        let operation_challenge =
            auth_info.finalize_create_authorization(Challenge(begin_result.challenge));

        let op_params: Vec<KeyParameter> = operation_parameters.to_vec();

        let (algorithm, _, _) = if let Some((_, ref props)) = key_properties {
            let km_props: Vec<KmKeyParameter> =
                props.iter().map(|kp| kp.clone().into_key_parameter()).collect();
            parse_key_parameters(&km_props)
        } else {
            parse_key_parameters(operation_parameters)
        };

        let operation = match begin_result.operation {
            Some(km_op) => self.operation_db.create_operation(
                km_op,
                caller_uid,
                auth_info,
                forced,
                LoggingInfo::new(
                    self.security_level,
                    purpose,
                    algorithm,
                    op_params,
                    upgraded_blob.is_some(),
                    is_attested,
                ),
            ),
            None => {
                return Err(Error::sys()).context(ks_err!(
                    "Begin operation returned successfully, \
                    but did not return a valid operation."
                ));
            }
        };

        let op_binder: binder::Strong<dyn IKeystoreOperation> =
            KeystoreOperation::new_native_binder(operation)
                .as_binder()
                .into_interface()
                .context(ks_err!("Failed to create IKeystoreOperation."))?;

        Ok(CreateOperationResponse {
            iOperation: Some(op_binder),
            operationChallenge: operation_challenge,
            parameters: match begin_result.params.len() {
                0 => None,
                _ => Some(KeyParameters { keyParameter: begin_result.params }),
            },
            // An upgraded blob should only be returned if the caller has permission
            // to use Domain::BLOB keys. If we got to this point, we already checked
            // that the caller had that permission.
            upgradedBlob: if key.domain == Domain::BLOB { upgraded_blob } else { None },
        })
    }

    fn add_required_parameters(
        &self,
        uid: AppUid,
        params: &[KeyParameter],
        key: &KeyDescriptor,
    ) -> Result<Vec<KeyParameter>> {
        let mut result = params.to_vec();

        // Prevent callers from specifying the CREATION_DATETIME tag.
        if params.iter().any(|kp| kp.tag == Tag::CREATION_DATETIME) {
            return Err(Error::Rc(ResponseCode::INVALID_ARGUMENT)).context(ks_err!(
                "KeystoreSecurityLevel::add_required_parameters: \
                Specifying Tag::CREATION_DATETIME is not allowed."
            ));
        }

        // Use this variable to refer to notion of "now". This eliminates discrepancies from
        // quering the clock multiple times.
        let creation_datetime = SystemTime::now();

        // Add CREATION_DATETIME only if the backend version Keymint V1 (100) or newer.
        if self.hw_info.versionNumber >= 100 {
            result.push(KeyParameter {
                tag: Tag::CREATION_DATETIME,
                value: KeyParameterValue::DateTime(
                    creation_datetime
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .context(ks_err!(
                            "KeystoreSecurityLevel::add_required_parameters: \
                                Failed to get epoch time."
                        ))?
                        .as_millis()
                        .try_into()
                        .context(ks_err!(
                            "KeystoreSecurityLevel::add_required_parameters: \
                                Failed to convert epoch time."
                        ))?,
                ),
            });
        }

        // If there is an attestation challenge we need to get an application id.
        if params.iter().any(|kp| kp.tag == Tag::ATTESTATION_CHALLENGE) {
            let _wp =
                self.watch(" KeystoreSecurityLevel::add_required_parameters: calling get_aaid");
            match keystore2_aaid::get_aaid(uid.0 as u32) {
                Ok(aaid_ok) => {
                    result.push(KeyParameter {
                        tag: Tag::ATTESTATION_APPLICATION_ID,
                        value: KeyParameterValue::Blob(aaid_ok),
                    });
                }
                Err(e) if e == ResponseCode::GET_ATTESTATION_APPLICATION_ID_FAILED.0 as u32 => {
                    return Err(Error::Rc(ResponseCode::GET_ATTESTATION_APPLICATION_ID_FAILED))
                        .context(ks_err!("Attestation ID retrieval failed."));
                }
                Err(e) => {
                    return Err(anyhow!(e)).context(ks_err!("Attestation ID retrieval error."));
                }
            }
        }

        if params.iter().any(|kp| kp.tag == Tag::INCLUDE_UNIQUE_ID) {
            if check_key_permission(KeyPerm::GenUniqueId, key, &None).is_err()
                && check_unique_id_attestation_permissions().is_err()
            {
                return Err(Error::perm()).context(ks_err!(
                    "Caller does not have the permission to generate a unique ID"
                ));
            }
            if self
                .id_rotation_state
                .had_factory_reset_since_id_rotation(&creation_datetime)
                .context(ks_err!("Call to had_factory_reset_since_id_rotation failed."))?
            {
                result.push(KeyParameter {
                    tag: Tag::RESET_SINCE_ID_ROTATION,
                    value: KeyParameterValue::BoolValue(true),
                })
            }
        }

        // If the caller requests any device identifier attestation tag, check that they hold the
        // correct Android permission.
        if params.iter().any(|kp| is_device_id_attestation_tag(kp.tag)) {
            check_device_attestation_permissions().context(ks_err!(
                "Caller does not have the permission to attest device identifiers."
            ))?;
        }

        // If we are generating/importing an asymmetric key, we need to make sure
        // that NOT_BEFORE and NOT_AFTER are present.
        match params.iter().find(|kp| kp.tag == Tag::ALGORITHM) {
            Some(KeyParameter { tag: _, value: KeyParameterValue::Algorithm(Algorithm::RSA) })
            | Some(KeyParameter { tag: _, value: KeyParameterValue::Algorithm(Algorithm::EC) })
            | Some(KeyParameter {
                tag: _,
                value: KeyParameterValue::Algorithm(Algorithm::ML_DSA),
            }) => {
                if !params.iter().any(|kp| kp.tag == Tag::CERTIFICATE_NOT_BEFORE) {
                    result.push(KeyParameter {
                        tag: Tag::CERTIFICATE_NOT_BEFORE,
                        value: KeyParameterValue::DateTime(0),
                    })
                }
                if !params.iter().any(|kp| kp.tag == Tag::CERTIFICATE_NOT_AFTER) {
                    result.push(KeyParameter {
                        tag: Tag::CERTIFICATE_NOT_AFTER,
                        value: KeyParameterValue::DateTime(UNDEFINED_NOT_AFTER),
                    })
                }
            }
            _ => {}
        }
        Ok(result)
    }

    /// Check whether new key generation should be failed due to excessive per-uid key counts.
    fn check_key_counts(&self, key: &KeyDescriptor) -> Result<()> {
        if !keystore2_flags::limit_keys_per_uid() {
            return Ok(());
        }
        if key.domain != Domain::APP {
            // Only limit app keys.
            return Ok(());
        }
        let uid = AppUid(key.nspace);

        // See how many keys this uid already owns.
        let Ok(count) =
            DB.with(|db| count_key_entries(&mut db.borrow_mut(), key.domain, key.nspace))
        else {
            // Fail open if we can't count the keys for some reason.
            error!("failed to count keys for {uid:?}");
            return Ok(());
        };

        // The per-uid limits for keys are based on the app's target SDK.
        // Determining the target SDK involves PackageManager round trips, so only
        // check target SDK if necessary.
        if count < API_37_PER_UID_KEY_LIMIT {
            // Below the lower limit => definitely OK.
            return Ok(());
        }
        let info = app_info_for_uid(uid);
        let targets_sdk37 = matches!(info.target_sdk, Some(target_sdk) if target_sdk >= 37);
        let limit = if info.is_system_app {
            // System apps get the higher limit.
            DEFAULT_PER_UID_KEY_LIMIT
        } else if targets_sdk37 {
            // Apps targeting SDK37+ get the lower limit.
            API_37_PER_UID_KEY_LIMIT
        } else {
            // Everything else gets the default (higher) limit.
            DEFAULT_PER_UID_KEY_LIMIT
        };

        if count >= limit {
            error!("failing key creation for {uid:?} with excessive ({count}) keys",);
            if targets_sdk37 {
                // Apps targeting SDK37+ can cope with the new error code.
                Err(error::Error::Rc(ResponseCode::TOO_MANY_APP_KEYS_SDK37)).context(ks_err!(
                    "failed key creation as {uid:?} (targeting SDK37+) has too many ({count}) existing keys",
                ))
            } else {
                Err(error::Error::Rc(ResponseCode::TOO_MANY_APP_KEYS)).context(ks_err!(
                    "failed key creation as {uid:?} has too many ({count}) existing keys",
                ))
            }
        } else {
            Ok(())
        }
    }

    // Generates a key and retries with swapped IMEI if an attestation ID mismatch error occurs.
    // This is a workaround for the fact that KeyMint was not required to support reordering
    // of IMEIs, even though the OS does not guarantee that the IMEI values are stably ordered.
    // This method can likely be safely removed in 34q2, once all devices still receiving
    // updates have KeyMint instances that are guaranteed to support this flexible ordering.
    fn generate_key_and_retry_on_att_id_mismatch(
        &self,
        params: &[KeyParameter],
        attest_key: Option<&AttestationKey>,
    ) -> Result<KeyCreationResult, Error> {
        let result = map_km_error({
            let _wp = self.watch_millis(
                "KeystoreSecurityLevel::generate_key: calling IKeyMintDevice::generateKey",
                5000,
            );
            self.keymint.generateKey(params, attest_key)
        });

        match &result {
            Err(Error::Km(ErrorCode::CANNOT_ATTEST_IDS))
            | Err(Error::Km(ErrorCode::INVALID_TAG))
            | Err(Error::Km(ErrorCode::ATTESTATION_IDS_NOT_PROVISIONED)) => {}
            _ => {
                // Not an error we can handle by retrying.
                return result;
            }
        }

        // The aforementioned errors might occur because the IMEI values are in the wrong order
        // which could only occur on KM instances that support multiple IMEIs in the first place.
        if self.hw_info.versionNumber < 300
            || self.hw_info.versionNumber >= 500
            || !params.iter().any(|p| crate::utils::is_imei_attestation_tag(p.tag))
        {
            return result;
        }

        // Try swapping the IMEI parameters, for those that are present.
        let swapped_params: Vec<KeyParameter> = params
            .iter()
            .map(|p| {
                let mut new_p = p.clone();
                match new_p.tag {
                    Tag::ATTESTATION_ID_IMEI => {
                        new_p.tag = Tag::ATTESTATION_ID_SECOND_IMEI;
                    }
                    Tag::ATTESTATION_ID_SECOND_IMEI => {
                        new_p.tag = Tag::ATTESTATION_ID_IMEI;
                    }
                    _ => {}
                }
                new_p
            })
            .collect();
        map_km_error({
            let _wp = self.watch_millis(
                concat!(
                    "KeystoreSecurityLevel::generate_key: calling ",
                    "IKeyMintDevice::generateKey, (retrying with swapped IMEIs)."
                ),
                5000,
            );
            self.keymint.generateKey(&swapped_params, attest_key)
        })
    }

    fn generate_key(
        &self,
        key: &KeyDescriptor,
        attest_key_descriptor: Option<&KeyDescriptor>,
        params: &[KeyParameter],
        flags: i32,
        _entropy: &[u8],
    ) -> Result<KeyMetadata> {
        if key.domain != Domain::BLOB && key.alias.is_none() {
            return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("Alias must be specified"));
        }
        let caller_uid = AppUid::calling();

        let key = match key.domain {
            Domain::APP => KeyDescriptor {
                domain: key.domain,
                nspace: caller_uid.0,
                alias: key.alias.clone(),
                blob: None,
            },
            _ => key.clone(),
        };
        self.check_key_counts(&key)?;

        // generate_key requires the rebind permission.
        // Must return on error for security reasons.
        check_key_permission(KeyPerm::Rebind, &key, &None).context(ks_err!())?;

        // Check the ORIGINAL request, including device-ID permissions, before the
        // scoped reply adapter derives the request sent to KeyMint.
        let params = self
            .add_required_parameters(caller_uid, params, &key)
            .context(ks_err!("Trying to get aaid."))?;
        // FundamentalOS: keystore2's appId provider only emits GMS's current signer; rebuild it with
        // GMS's full signing history before KeyMint so the resulting attestation matches what Google
        // validates (this was the only field that differed from a TrickyStoreOSS-forged leaf).
        let params = crate::attest_spoof::augment_app_id(&params);
        let spoof_ctx = crate::attest_spoof::capture(caller_uid.0 as u32, &params);
        // FundamentalOS: device-ID attestation is rejected by real KeyMint (CANNOT_ATTEST_IDS), and
        // leaf-hacking a real key drags in the RKP-failing hardware path DroidGuard can observe.
        // Forge a software-backed key + keybox attestation instead (mirrors TrickyStoreOSS forge).
        if let Some(ctx) = spoof_ctx.as_ref() {
            if crate::attest_spoof::wants_device_id_attestation(&params) {
                match self.forge_software_key(&params, ctx, caller_uid.0 as u32) {
                    Ok(creation_result) => {
                        let user = caller_uid.owning_user();
                        return self
                            .store_new_key(key, creation_result, user, Some(flags))
                            .context(ks_err!("Storing forged software-backed key."));
                    }
                    Err(e) => {
                        log::error!("attest_spoof: software forge failed ({e:?}); using real KeyMint")
                    }
                }
            }
        }
        let params = crate::attest_spoof::keymint_params(&params, spoof_ctx.as_ref());

        let attestation_key_info = match (key.domain, attest_key_descriptor) {
            (Domain::BLOB, _) => None,
            _ => DB
                .with(|db| {
                    get_attest_key_info(
                        &key,
                        caller_uid,
                        attest_key_descriptor,
                        &params,
                        &self.rem_prov_state,
                        &mut db.borrow_mut(),
                    )
                })
                .context(ks_err!("Trying to get an attestation key"))?,
        };
        let mut creation_result = match attestation_key_info {
            Some(AttestationKeyInfo::UserGenerated {
                key_id_guard,
                blob,
                blob_metadata,
                issuer_subject,
            }) => self
                .upgrade_keyblob_if_required_with(
                    Some(key_id_guard),
                    &KeyBlob::Ref(&blob),
                    blob_metadata.km_uuid().copied(),
                    &params,
                    |blob| {
                        let attest_key = Some(AttestationKey {
                            keyBlob: blob.to_vec(),
                            attestKeyParams: vec![],
                            issuerSubjectName: issuer_subject.clone(),
                        });
                        self.generate_key_and_retry_on_att_id_mismatch(&params, attest_key.as_ref())
                    },
                )
                .context(ks_err!(
                    "While generating with a user-generated \
                      attestation key, params: {:?}.",
                    log_security_safe_params(&params)
                ))
                .map(|(result, _)| result),
            Some(AttestationKeyInfo::RkpdProvisioned { attestation_key, attestation_certs }) => {
                self.upgrade_rkpd_keyblob_if_required_with(&attestation_key.keyBlob, &[], |blob| {
                    let dynamic_attest_key = Some(AttestationKey {
                        keyBlob: blob.to_vec(),
                        attestKeyParams: vec![],
                        issuerSubjectName: attestation_key.issuerSubjectName.clone(),
                    });
                    self.generate_key_and_retry_on_att_id_mismatch(
                        &params,
                        dynamic_attest_key.as_ref(),
                    )
                })
                .context(ks_err!(
                    "While generating Key {:?} with remote \
                    provisioned attestation key and params: {:?}.",
                    key.alias,
                    log_security_safe_params(&params)
                ))
                .map(|(mut result, _)| {
                    if read_bool("remote_provisioning.use_cert_processor", false).unwrap_or(false) {
                        let _wp = self.watch_millis(
                            concat!(
                                "KeystoreSecurityLevel::generate_key (RkpdProvisioned): ",
                                "calling KeystorePostProcessor::process_certificate_chain",
                            ),
                            1000, // Post processing may take a little while due to network call.
                        );
                        // process_certificate_chain would either replace the certificate chain if
                        // post-processing is successful or it would fallback to the original chain
                        // on failure. In either case, we should get back the certificate chain
                        // that is fit for storing with the newly generated key.
                        result.certificateChain =
                            process_certificate_chain(result.certificateChain, attestation_certs);
                    } else {
                        // The `certificateChain` in a `KeyCreationResult` should normally have one
                        // `Certificate` for each certificate in the chain. To avoid having to
                        // unnecessarily parse the RKP chain (which is concatenated DER-encoded
                        // certs), stuff the whole concatenated chain into a single `Certificate`.
                        // This is untangled by `store_new_key()`.
                        result
                            .certificateChain
                            .push(Certificate { encodedCertificate: attestation_certs });
                    }
                    result
                })
            }
            None => self.generate_key_and_retry_on_att_id_mismatch(&params, None).context(ks_err!(
                "While generating without a provided \
                 attestation key and params: {:?}.",
                log_security_safe_params(&params)
            )),
        }
        .context(ks_err!())?;

        // FundamentalOS: observe-only dump of REAL KeyMint attestation for OBSERVE_PATH uids.
        crate::attest_spoof::observe_dump(caller_uid.0 as u32, &creation_result);

        // FundamentalOS: selective per-app keybox attestation substitution (Play Integrity DEVICE).
        // FundamentalOS: synthesize keybox attestation for targeted uids.
        if let Some(ctx) = &spoof_ctx {
            crate::attest_spoof::synthesize(&mut creation_result, ctx, caller_uid.0 as u32);
        }
        let user = caller_uid.owning_user();
        self.store_new_key(key, creation_result, user, Some(flags)).context(ks_err!())
    }

    fn import_key(
        &self,
        key: &KeyDescriptor,
        _attestation_key: Option<&KeyDescriptor>,
        params: &[KeyParameter],
        flags: i32,
        key_data: &[u8],
    ) -> Result<KeyMetadata> {
        if key.domain != Domain::BLOB && key.alias.is_none() {
            return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("Alias must be specified"));
        }
        let caller_uid = AppUid::calling();

        let key = match key.domain {
            Domain::APP => KeyDescriptor {
                domain: key.domain,
                nspace: caller_uid.0,
                alias: key.alias.clone(),
                blob: None,
            },
            _ => key.clone(),
        };
        self.check_key_counts(&key)?;

        // import_key requires the rebind permission.
        check_key_permission(KeyPerm::Rebind, &key, &None).context(ks_err!("In import_key."))?;

        let params = self
            .add_required_parameters(caller_uid, params, &key)
            .context(ks_err!("Trying to get aaid."))?;

        let format = params
            .iter()
            .find(|p| p.tag == Tag::ALGORITHM)
            .ok_or(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
            .context(ks_err!("No KeyParameter 'Algorithm'."))
            .and_then(|p| match &p.value {
                KeyParameterValue::Algorithm(Algorithm::AES)
                | KeyParameterValue::Algorithm(Algorithm::HMAC)
                | KeyParameterValue::Algorithm(Algorithm::TRIPLE_DES) => Ok(KeyFormat::RAW),
                KeyParameterValue::Algorithm(Algorithm::RSA)
                | KeyParameterValue::Algorithm(Algorithm::EC)
                | KeyParameterValue::Algorithm(Algorithm::ML_DSA) => Ok(KeyFormat::PKCS8),
                v => Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                    .context(ks_err!("Unknown Algorithm {:?}.", v)),
            })
            .context(ks_err!())?;

        let km_dev = &self.keymint;
        let creation_result = map_km_error({
            let _wp =
                self.watch("KeystoreSecurityLevel::import_key: calling IKeyMintDevice::importKey.");
            km_dev.importKey(&params, format, key_data, None /* attestKey */)
        })
        .context(ks_err!("Trying to call importKey"))?;

        let user = caller_uid.owning_user();
        self.store_new_key(key, creation_result, user, Some(flags)).context(ks_err!())
    }

    fn import_wrapped_key(
        &self,
        key: &KeyDescriptor,
        wrapping_key: &KeyDescriptor,
        masking_key: Option<&[u8]>,
        params: &[KeyParameter],
        authenticators: &[AuthenticatorSpec],
    ) -> Result<KeyMetadata> {
        let wrapped_data: &[u8] = match key {
            KeyDescriptor { domain: Domain::APP, blob: Some(ref blob), alias: Some(_), .. }
            | KeyDescriptor {
                domain: Domain::SELINUX, blob: Some(ref blob), alias: Some(_), ..
            } => blob,
            _ => {
                return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT)).context(ks_err!(
                    "Alias and blob must be specified and domain must be APP or SELINUX. {:?}",
                    key
                ));
            }
        };

        if wrapping_key.domain == Domain::BLOB {
            return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("Import wrapped key not supported for self managed blobs."));
        }

        let caller_uid = AppUid::calling();

        let key = match key.domain {
            Domain::APP => KeyDescriptor {
                domain: key.domain,
                nspace: caller_uid.0,
                alias: key.alias.clone(),
                blob: None,
            },
            Domain::SELINUX => KeyDescriptor {
                domain: Domain::SELINUX,
                nspace: key.nspace,
                alias: key.alias.clone(),
                blob: None,
            },
            _ => panic!("Unreachable."),
        };
        self.check_key_counts(&key)?;

        // Import_wrapped_key requires the rebind permission for the new key.
        check_key_permission(KeyPerm::Rebind, &key, &None).context(ks_err!())?;

        let user = caller_uid.owning_user();
        let super_key = SUPER_KEY.read().unwrap().get_credential_encrypted_key_by_user_id(user);

        let (wrapping_key_id_guard, mut wrapping_key_entry) = DB
            .with(|db| {
                LEGACY_IMPORTER.with_try_import(&key, caller_uid, super_key, || {
                    db.borrow_mut().load_key_entry(
                        wrapping_key,
                        KeyType::Client,
                        KeyEntryLoadBits::KM,
                        caller_uid,
                        |k, av| check_key_permission(KeyPerm::Use, k, &av),
                    )
                })
            })
            .context(ks_err!("Failed to load wrapping key."))?;

        let (wrapping_key_blob, wrapping_blob_metadata) =
            wrapping_key_entry.take_key_blob_info().ok_or_else(error::Error::sys).context(
                ks_err!("No km_blob after successfully loading key. This should never happen."),
            )?;

        let wrapping_key_blob = SUPER_KEY
            .read()
            .unwrap()
            .unwrap_key_if_required(&wrapping_blob_metadata, &wrapping_key_blob)
            .context(ks_err!("Failed to handle super encryption for wrapping key."))?;

        // km_dev.importWrappedKey does not return a certificate chain.
        // TODO Do we assume that all wrapped keys are symmetric?
        // let certificate_chain: Vec<KmCertificate> = Default::default();

        let pw_sid = authenticators
            .iter()
            .find_map(|a| match a.authenticatorType {
                HardwareAuthenticatorType::PASSWORD => Some(a.authenticatorId),
                _ => None,
            })
            .unwrap_or(-1);

        let fp_sid = authenticators
            .iter()
            .find_map(|a| match a.authenticatorType {
                HardwareAuthenticatorType::FINGERPRINT => Some(a.authenticatorId),
                _ => None,
            })
            .unwrap_or(-1);

        let masking_key = masking_key.unwrap_or(ZERO_BLOB_32);

        let (creation_result, _) = self
            .upgrade_keyblob_if_required_with(
                Some(wrapping_key_id_guard),
                &wrapping_key_blob,
                wrapping_blob_metadata.km_uuid().copied(),
                &[],
                |wrapping_blob| {
                    let _wp = self.watch(
                        "KeystoreSecurityLevel::import_wrapped_key: calling IKeyMintDevice::importWrappedKey.",
                    );
                    let creation_result = map_km_error(self.keymint.importWrappedKey(
                        wrapped_data,
                        wrapping_blob,
                        masking_key,
                        params,
                        pw_sid,
                        fp_sid,
                    ))?;
                    Ok(creation_result)
                },
            )
            .context(ks_err!())?;

        self.store_new_key(key, creation_result, user, None)
            .context(ks_err!("Trying to store the new key for {user:?}"))
    }

    fn store_upgraded_keyblob(
        key_id_guard: KeyIdGuard,
        km_uuid: Option<Uuid>,
        key_blob: &KeyBlob,
        upgraded_blob: &[u8],
    ) -> Result<()> {
        let (upgraded_blob_to_be_stored, new_blob_metadata) =
            SuperKeyManager::reencrypt_if_required(key_blob, upgraded_blob)
                .context(ks_err!("Failed to handle super encryption."))?;

        let mut new_blob_metadata = new_blob_metadata.unwrap_or_default();
        if let Some(uuid) = km_uuid {
            new_blob_metadata.add(BlobMetaEntry::KmUuid(uuid));
        }

        DB.with(|db| {
            let mut db = db.borrow_mut();
            db.set_blob(
                &key_id_guard,
                SubComponentType::KEY_BLOB,
                Some(&upgraded_blob_to_be_stored),
                Some(&new_blob_metadata),
            )
        })
        .context(ks_err!("Failed to insert upgraded blob into the database."))
    }

    fn upgrade_keyblob_if_required_with<T, F>(
        &self,
        mut key_id_guard: Option<KeyIdGuard>,
        key_blob: &KeyBlob,
        km_uuid: Option<Uuid>,
        params: &[KeyParameter],
        f: F,
    ) -> Result<(T, Option<Vec<u8>>)>
    where
        F: Fn(&[u8]) -> Result<T, Error>,
    {
        let (v, upgraded_blob) = crate::utils::upgrade_keyblob_if_required_with(
            &*self.keymint,
            self.hw_info.versionNumber,
            key_blob,
            params,
            f,
            |upgraded_blob| {
                if key_id_guard.is_some() {
                    // Unwrap cannot panic, because the is_some was true.
                    let kid = key_id_guard.take().unwrap();
                    Self::store_upgraded_keyblob(kid, km_uuid, key_blob, upgraded_blob)
                        .context(ks_err!("store_upgraded_keyblob failed"))
                } else {
                    Ok(())
                }
            },
        )
        .context(ks_err!("upgrade_keyblob_if_required_with(key_id={:?})", key_id_guard))?;

        // If no upgrade was needed, use the opportunity to reencrypt the blob if required
        // and if the a key_id_guard is held. Note: key_id_guard can only be Some if no
        // upgrade was performed above and if one was given in the first place.
        if key_blob.force_reencrypt() {
            if let Some(kid) = key_id_guard {
                Self::store_upgraded_keyblob(kid, km_uuid, key_blob, key_blob)
                    .context(ks_err!("store_upgraded_keyblob failed in forced reencrypt"))?;
            }
        }
        Ok((v, upgraded_blob))
    }

    fn upgrade_rkpd_keyblob_if_required_with<T, F>(
        &self,
        key_blob: &[u8],
        params: &[KeyParameter],
        f: F,
    ) -> Result<(T, Option<Vec<u8>>)>
    where
        F: Fn(&[u8]) -> Result<T, Error>,
    {
        let rpc_name = get_remotely_provisioned_component_name(&self.security_level)
            .context(ks_err!("Trying to get IRPC name."))?;
        crate::utils::upgrade_keyblob_if_required_with(
            &*self.keymint,
            self.hw_info.versionNumber,
            key_blob,
            params,
            f,
            |upgraded_blob| {
                let _wp = wd::watch("Calling store_rkpd_attestation_key()");
                if let Err(e) = store_rkpd_attestation_key(&rpc_name, key_blob, upgraded_blob) {
                    Err(wrapped_rkpd_error_to_ks_error(&e)).context(format!("{e:?}"))
                } else {
                    Ok(())
                }
            },
        )
        .context(ks_err!(
            "upgrade_rkpd_keyblob_if_required_with(params={:?})",
            log_security_safe_params(params)
        ))
    }

    fn convert_storage_key_to_ephemeral(
        &self,
        storage_key: &KeyDescriptor,
    ) -> Result<EphemeralStorageKeyResponse> {
        if storage_key.domain != Domain::BLOB {
            return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("Key must be of Domain::BLOB"));
        }
        let key_blob = storage_key
            .blob
            .as_ref()
            .ok_or(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
            .context(ks_err!("No key blob specified"))?;

        // convert_storage_key_to_ephemeral requires the associated permission
        check_key_permission(KeyPerm::ConvertStorageKeyToEphemeral, storage_key, &None)
            .context(ks_err!("Check permission"))?;

        let km_dev = &self.keymint;
        let res = {
            let _wp = self.watch(concat!(
                "IKeystoreSecurityLevel::convert_storage_key_to_ephemeral: ",
                "calling IKeyMintDevice::convertStorageKeyToEphemeral (1)"
            ));
            map_km_error(km_dev.convertStorageKeyToEphemeral(key_blob))
        };
        match res {
            Ok(result) => {
                Ok(EphemeralStorageKeyResponse { ephemeralKey: result, upgradedBlob: None })
            }
            Err(error::Error::Km(ErrorCode::KEY_REQUIRES_UPGRADE)) => {
                let upgraded_blob = {
                    let _wp = self.watch("IKeystoreSecurityLevel::convert_storage_key_to_ephemeral: calling IKeyMintDevice::upgradeKey");
                    map_km_error(km_dev.upgradeKey(key_blob, &[]))
                }
                .context(ks_err!("Failed to upgrade key blob."))?;
                let ephemeral_key = {
                    let _wp = self.watch(concat!(
                        "IKeystoreSecurityLevel::convert_storage_key_to_ephemeral: ",
                        "calling IKeyMintDevice::convertStorageKeyToEphemeral (2)"
                    ));
                    map_km_error(km_dev.convertStorageKeyToEphemeral(&upgraded_blob))
                }
                .context(ks_err!("Failed to retrieve ephemeral key (after upgrade)."))?;
                Ok(EphemeralStorageKeyResponse {
                    ephemeralKey: ephemeral_key,
                    upgradedBlob: Some(upgraded_blob),
                })
            }
            Err(e) => Err(e).context(ks_err!("Failed to retrieve ephemeral key.")),
        }
    }

    fn delete_key(&self, key: &KeyDescriptor) -> Result<()> {
        if key.domain != Domain::BLOB {
            return Err(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
                .context(ks_err!("delete_key: Key must be of Domain::BLOB"));
        }

        let key_blob = key
            .blob
            .as_ref()
            .ok_or(error::Error::Km(ErrorCode::INVALID_ARGUMENT))
            .context(ks_err!("delete_key: No key blob specified"))?;

        check_key_permission(KeyPerm::Delete, key, &None)
            .context(ks_err!("delete_key: Checking delete permissions"))?;

        let km_dev = &self.keymint;
        {
            let _wp =
                self.watch("KeystoreSecuritylevel::delete_key: calling IKeyMintDevice::deleteKey");
            map_km_error(km_dev.deleteKey(key_blob)).context(ks_err!("keymint device deleteKey"))
        }
    }
}

impl binder::Interface for KeystoreSecurityLevel {}

impl IKeystoreSecurityLevel for KeystoreSecurityLevel {
    fn createOperation(
        &self,
        key: &KeyDescriptor,
        operation_parameters: &[KeyParameter],
        forced: bool,
    ) -> binder::Result<CreateOperationResponse> {
        crate::attest_spoof::ks_trace(&format!("createOperation(secLvl={}, alias={:?}, purposes={:?})", self.security_level.0, key.alias, operation_parameters.iter().filter(|p| p.tag == Tag::PURPOSE).map(|p| format!("{:?}", p.value)).collect::<Vec<_>>()), ThreadState::get_calling_uid());
        let _wp = self.watch("IKeystoreSecurityLevel::createOperation");
        security_level_manager::notify_operation_performed(self.security_level);
        let (latency, result) =
            crate::timed_call!(self.create_operation(key, operation_parameters, forced));
        log_operation_latency(
            OperationType::CREATE_OPERATION,
            self.security_level,
            operation_parameters,
            result.is_ok(),
            latency,
        );
        crate::attest_spoof::ks_trace(&format!("  -> createOperation ok={}", result.is_ok()), ThreadState::get_calling_uid());
        result.map_err(into_logged_binder)
    }
    fn generateKey(
        &self,
        key: &KeyDescriptor,
        attestation_key: Option<&KeyDescriptor>,
        params: &[KeyParameter],
        flags: i32,
        entropy: &[u8],
    ) -> binder::Result<KeyMetadata> {
        crate::attest_spoof::ks_trace(&format!("generateKey(secLvl={}, alias={:?}, attKey={})", self.security_level.0, key.alias, attestation_key.is_some()), ThreadState::get_calling_uid());
        // Duration is set to 5 seconds, because generateKey - especially for RSA keys, takes more
        // time than other operations
        let _wp = self.watch_millis("IKeystoreSecurityLevel::generateKey", 5000);
        security_level_manager::notify_operation_performed(self.security_level);
        let (latency, result) =
            crate::timed_call!(self.generate_key(key, attestation_key, params, flags, entropy));
        log_key_creation_event_stats(
            AppUid::calling().0 as i32,
            self.security_level,
            params,
            KeyOrigin::GENERATED,
            &result,
        );
        log_operation_latency(
            OperationType::GENERATE_KEY,
            self.security_level,
            params,
            result.is_ok(),
            latency,
        );
        log_key_generated(key, ThreadState::get_calling_uid(), result.is_ok());
        result.map_err(into_logged_binder)
    }
    fn importKey(
        &self,
        key: &KeyDescriptor,
        attestation_key: Option<&KeyDescriptor>,
        params: &[KeyParameter],
        flags: i32,
        key_data: &[u8],
    ) -> binder::Result<KeyMetadata> {
        crate::attest_spoof::ks_trace("importKey", ThreadState::get_calling_uid());
        let _wp = self.watch("IKeystoreSecurityLevel::importKey");
        security_level_manager::notify_operation_performed(self.security_level);
        let (latency, result) =
            crate::timed_call!(self.import_key(key, attestation_key, params, flags, key_data));
        log_key_creation_event_stats(
            AppUid::calling().0 as i32,
            self.security_level,
            params,
            KeyOrigin::IMPORTED,
            &result,
        );
        log_operation_latency(
            OperationType::IMPORT_KEY,
            self.security_level,
            params,
            result.is_ok(),
            latency,
        );
        log_key_imported(key, ThreadState::get_calling_uid(), result.is_ok());
        result.map_err(into_logged_binder)
    }
    fn importWrappedKey(
        &self,
        key: &KeyDescriptor,
        wrapping_key: &KeyDescriptor,
        masking_key: Option<&[u8]>,
        params: &[KeyParameter],
        authenticators: &[AuthenticatorSpec],
    ) -> binder::Result<KeyMetadata> {
        crate::attest_spoof::ks_trace("importWrappedKey", ThreadState::get_calling_uid());
        let _wp = self.watch("IKeystoreSecurityLevel::importWrappedKey");
        security_level_manager::notify_operation_performed(self.security_level);
        let (latency, result) = crate::timed_call!(self.import_wrapped_key(
            key,
            wrapping_key,
            masking_key,
            params,
            authenticators
        ));
        log_key_creation_event_stats(
            AppUid::calling().0 as i32,
            self.security_level,
            params,
            KeyOrigin::SECURELY_IMPORTED,
            &result,
        );
        log_operation_latency(
            OperationType::IMPORT_WRAPPED_KEY,
            self.security_level,
            params,
            result.is_ok(),
            latency,
        );
        log_key_imported(key, ThreadState::get_calling_uid(), result.is_ok());
        result.map_err(into_logged_binder)
    }
    fn convertStorageKeyToEphemeral(
        &self,
        storage_key: &KeyDescriptor,
    ) -> binder::Result<EphemeralStorageKeyResponse> {
        crate::attest_spoof::ks_trace("convertStorageKeyToEphemeral", ThreadState::get_calling_uid());
        let _wp = self.watch("IKeystoreSecurityLevel::convertStorageKeyToEphemeral");
        security_level_manager::notify_operation_performed(self.security_level);
        self.convert_storage_key_to_ephemeral(storage_key).map_err(into_logged_binder)
    }
    fn deleteKey(&self, key: &KeyDescriptor) -> binder::Result<()> {
        crate::attest_spoof::ks_trace("SecLvl::deleteKey", ThreadState::get_calling_uid());
        let _wp = self.watch("IKeystoreSecurityLevel::deleteKey");
        security_level_manager::notify_operation_performed(self.security_level);
        let result = self.delete_key(key);
        log_key_deleted(key, ThreadState::get_calling_uid(), result.is_ok());
        result.map_err(into_logged_binder)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::map_km_error;
    use crate::globals::get_keymint_device;
    use crate::utils::upgrade_keyblob_if_required_with;
    use android_hardware_security_keymint::aidl::android::hardware::security::keymint::{
        Algorithm::Algorithm, AttestationKey::AttestationKey, KeyParameter::KeyParameter,
        KeyParameterValue::KeyParameterValue, Tag::Tag,
    };
    use keystore2_crypto::parse_subject_from_certificate;
    use rkpd_client::get_rkpd_attestation_key;

    #[test]
    // This is a helper for a manual test. We want to check that after a system upgrade RKPD
    // attestation keys can also be upgraded and stored again with RKPD. The steps are:
    // 1. Run this test and check in stdout that no key upgrade happened.
    // 2. Perform a system upgrade.
    // 3. Run this test and check in stdout that key upgrade did happen.
    //
    // Note that this test must be run with that same UID every time. Running as root, i.e. UID 0,
    // should do the trick. Also, use "--nocapture" flag to get stdout.
    fn test_rkpd_attestation_key_upgrade() {
        binder::ProcessState::start_thread_pool();
        let security_level = SecurityLevel::TRUSTED_ENVIRONMENT;
        let (keymint, info, _) = get_keymint_device(&security_level).unwrap();
        let key_id = 0;
        let mut key_upgraded = false;

        let rpc_name = get_remotely_provisioned_component_name(&security_level).unwrap();
        let key = get_rkpd_attestation_key(&rpc_name, key_id).unwrap();
        assert!(!key.keyBlob.is_empty());
        assert!(!key.encodedCertChain.is_empty());

        upgrade_keyblob_if_required_with(
            &*keymint,
            info.versionNumber,
            &key.keyBlob,
            /*upgrade_params=*/ &[],
            /*km_op=*/
            |blob| {
                let params = vec![
                    KeyParameter {
                        tag: Tag::ALGORITHM,
                        value: KeyParameterValue::Algorithm(Algorithm::AES),
                    },
                    KeyParameter {
                        tag: Tag::ATTESTATION_CHALLENGE,
                        value: KeyParameterValue::Blob(vec![0; 16]),
                    },
                    KeyParameter { tag: Tag::KEY_SIZE, value: KeyParameterValue::Integer(128) },
                ];
                let attestation_key = AttestationKey {
                    keyBlob: blob.to_vec(),
                    attestKeyParams: vec![],
                    issuerSubjectName: parse_subject_from_certificate(&key.encodedCertChain)
                        .unwrap(),
                };

                map_km_error(keymint.generateKey(&params, Some(&attestation_key)))
            },
            /*new_blob_handler=*/
            |new_blob| {
                // This handler is only executed if a key upgrade was performed.
                key_upgraded = true;
                let _wp = wd::watch("Calling store_rkpd_attestation_key()");
                store_rkpd_attestation_key(&rpc_name, &key.keyBlob, new_blob).unwrap();
                Ok(())
            },
        )
        .unwrap();

        if key_upgraded {
            println!("RKPD key was upgraded and stored with RKPD.");
        } else {
            println!("RKPD key was NOT upgraded.");
        }
    }
}
