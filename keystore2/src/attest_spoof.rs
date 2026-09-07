// FundamentalOS: selective per-app keybox attestation SYNTHESIS (Android 16 compatible).
//
//! For UIDs in `/data/misc/fundamental/targets.txt`, we strip the attestation challenge before the
//! KeyMint call (so KeyMint emits a plain self-signed leaf, no RKP dependency), then synthesize a
//! full keybox-signed attestation leaf from scratch — including the A16 MODULE_HASH ([724])
//! extension — so those apps get MEETS_DEVICE/STRONG_INTEGRITY. Mirrors TrickyStoreOSS CertHack.
//! Fail-open: any error leaves the genuine result untouched.
#![allow(dead_code)]

use android_hardware_security_keymint::aidl::android::hardware::security::keymint::{
    Algorithm::Algorithm, Certificate::Certificate as KmCertificate, Digest::Digest,
    EcCurve::EcCurve, KeyCreationResult::KeyCreationResult,
    KeyParameter::KeyParameter, KeyParameterValue::KeyParameterValue, KeyPurpose::KeyPurpose,
    SecurityLevel::SecurityLevel, Tag::Tag,
};
use android_system_keystore2::aidl::android::system::keystore2::{
    Authorization::Authorization, KeyMetadata::KeyMetadata,
};
use der::asn1::{BitString, OctetString};
use der::{Decode, Encode};
use spki::AlgorithmIdentifierOwned;
use std::collections::HashSet;
use std::sync::{LazyLock, Mutex};
use x509_cert::ext::Extension;
use x509_cert::Certificate;
use const_oid::ObjectIdentifier;

// FundamentalOS integrity config, written by Settings (fundamental_data_file), read here. targets.txt
// holds the target UIDs (empty/absent = forge disabled); keybox.xml is the user-imported keybox.
const KEYBOX_PATH: &str = "/data/misc/fundamental/keybox.xml";
const TARGET_PATH: &str = "/data/misc/fundamental/targets.txt";
const OBSERVE_PATH: &str = "/data/misc/fundamental/observe.txt";

const EC_PUBKEY_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.2.840.10045.2.1");
const ATTEST_EXT_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.6.1.4.1.11129.2.1.17");
const KEY_USAGE_OID: ObjectIdentifier = ObjectIdentifier::new_unwrap("2.5.29.15");
// KeyUsage BIT STRING: digitalSignature only (7 unused bits, 0x80).
const KEY_USAGE_DIGSIG: &[u8] = &[0x03, 0x02, 0x07, 0x80];

const ALGID_ECDSA_SHA256: &[u8] =
    &[0x30, 0x0A, 0x06, 0x08, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02];
const ALGID_SHA256_RSA: &[u8] =
    &[0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x0B, 0x05, 0x00];

struct KeyEntry { private_key_pem: String, chain_pem: Vec<String> }
struct Keybox { ec: Option<KeyEntry>, rsa: Option<KeyEntry> }

// NOTE: NOT a bare OnceLock. A OnceLock caches the FIRST load — and the first is_target() call can
// happen at early boot before /data/misc/fundamental is readable, caching an EMPTY target set (or a None
// keybox) for the whole keystore2 process, silently making the forge inert until the next restart.
// These retry the load until it yields a usable value (see is_target()/keybox()).
static KEYBOX: LazyLock<Mutex<Option<&'static Keybox>>> = LazyLock::new(|| Mutex::new(None));
static TARGETS: LazyLock<Mutex<Option<(Option<std::time::SystemTime>, HashSet<u32>)>>> =
    LazyLock::new(|| Mutex::new(None));

/// Captured attestation request for a targeted uid.
pub struct SpoofCtx {
    challenge: Vec<u8>,
    app_id: Vec<u8>,
    key_size: i64,
    algorithm: i64,
    ec_curve: i64,
    digests: Vec<i64>,
    purposes: Vec<i64>,
    os_version: i64,
    os_patch: i64,
    vendor_patch: i64,
    boot_patch: i64,
    brand: Vec<u8>,
    device: Vec<u8>,
    product: Vec<u8>,
    manufacturer: Vec<u8>,
    model: Vec<u8>,
    device_ids: Vec<(u32, Vec<u8>)>,
}

/// True if `uid` is in the target list. Reloads targets.txt whenever its mtime changes (and while
/// the cached set is empty), so enabling, disabling, or editing the target set from Settings takes
/// effect on the next attestation without a keystore2 restart, and a transient early-boot read
/// failure is retried instead of being cached as "no targets" forever.
pub fn is_target(uid: u32) -> bool {
    let mtime = std::fs::metadata(TARGET_PATH).and_then(|m| m.modified()).ok();
    let mut g = TARGETS.lock().unwrap();
    let stale = match g.as_ref() {
        Some((cached_mtime, set)) => *cached_mtime != mtime || set.is_empty(),
        None => true,
    };
    if stale {
        *g = Some((mtime, load_targets()));
    }
    g.as_ref().is_some_and(|(_, s)| s.contains(&uid))
}

/// The loaded keybox. Like is_target(), retries load_keybox() until it succeeds (instead of caching
/// a boot-time None forever). Leaked once so callers get a cheap 'static reference.
fn keybox() -> Option<&'static Keybox> {
    let mut g = KEYBOX.lock().unwrap();
    if g.is_none() {
        if let Some(kb) = load_keybox() {
            let leaked: &'static Keybox = Box::leak(Box::new(kb));
            *g = Some(leaked);
        }
    }
    *g
}

/// Debug: trace every keystore2 binder method a targeted uid (GMS) calls, so we can see what
/// DroidGuard does beyond generateKey (which TrickyStoreOSS's full binder interception covers).
pub fn ks_trace(method: &str, uid: u32) {
    if is_target(uid) {
        log::info!("KS_TRACE: {} uid={}", method, uid);
    }
}

/// Called at the top of generate_key: if this uid is targeted and the params carry an attestation
/// challenge, capture what we need to synthesize later. Returns None to leave the flow untouched.
pub fn capture(uid: u32, params: &[KeyParameter]) -> Option<SpoofCtx> {
    if !is_target(uid) { return None; }
    let challenge = get_blob(params, Tag::ATTESTATION_CHALLENGE)?;
    // Leave requests untouched if the configured signing material is unavailable.
    keybox()?;
    let app_id = get_blob(params, Tag::ATTESTATION_APPLICATION_ID).unwrap_or_default();
    let patch = read_patch_levels();
    Some(SpoofCtx {
        challenge,
        app_id,
        key_size: get_int(params, Tag::KEY_SIZE).unwrap_or(256),
        algorithm: get_algo(params).unwrap_or(3), // EC
        ec_curve: get_ec_curve(params).unwrap_or(1), // P_256
        digests: get_digests(params),
        purposes: get_purposes(params),
        os_version: 160000,
        os_patch: patch.0,
        vendor_patch: patch.1,
        boot_patch: patch.1,
        brand: get_blob(params, Tag::ATTESTATION_ID_BRAND).unwrap_or_default(),
        device: get_blob(params, Tag::ATTESTATION_ID_DEVICE).unwrap_or_default(),
        product: get_blob(params, Tag::ATTESTATION_ID_PRODUCT).unwrap_or_default(),
        manufacturer: get_blob(params, Tag::ATTESTATION_ID_MANUFACTURER).unwrap_or_default(),
        model: get_blob(params, Tag::ATTESTATION_ID_MODEL).unwrap_or_default(),
        device_ids: params.iter().filter_map(|p| {
            if !is_unique_device_id(p.tag) { return None; }
            match &p.value {
                KeyParameterValue::Blob(value) => Some(((p.tag.0 as u32) & 0x0fff_ffff, value.clone())),
                _ => None,
            }
        }).collect(),
    })
}

/// Tags for which TSOSS SecurityLevelInterceptor selects its generated-certificate path.
/// General device properties (brand/model/etc.) remain enforced by KeyMint.
fn is_unique_device_id(tag: Tag) -> bool {
    matches!(tag, Tag::ATTESTATION_ID_SERIAL | Tag::ATTESTATION_ID_IMEI
        | Tag::ATTESTATION_ID_MEID | Tag::ATTESTATION_ID_SECOND_IMEI)
}

/// Any ATTESTATION_ID_* tag (unique IDs + brand/model/etc.). These are stripped before the
/// software KeyMint call so it emits a plain key; we then forge the attestation with them.
fn is_attestation_id_tag(tag: Tag) -> bool {
    is_unique_device_id(tag)
        || matches!(tag, Tag::ATTESTATION_ID_BRAND | Tag::ATTESTATION_ID_DEVICE
            | Tag::ATTESTATION_ID_PRODUCT | Tag::ATTESTATION_ID_MANUFACTURER | Tag::ATTESTATION_ID_MODEL)
}

/// True if the request asks to attest a UNIQUE device ID (IMEI/MEID/SERIAL/SECOND_IMEI). Real
/// KeyMint on an unlocked device rejects these with CANNOT_ATTEST_IDS, so — like TrickyStoreOSS's
/// forceForge path — we forge a software-backed key instead of leaf-hacking the real one.
pub fn wants_device_id_attestation(params: &[KeyParameter]) -> bool {
    params.iter().any(|p| is_unique_device_id(p.tag))
}

/// Strip the attestation challenge and every ATTESTATION_ID_* tag so a plain (non-attesting) key
/// generation succeeds on the software KeyMint. Everything else (algorithm, purpose, digest…) stays.
pub fn software_keygen_params(params: &[KeyParameter]) -> Vec<KeyParameter> {
    params.iter()
        .filter(|p| p.tag != Tag::ATTESTATION_CHALLENGE
            && p.tag != Tag::ATTESTATION_APPLICATION_ID
            && p.tag != Tag::DEVICE_UNIQUE_ATTESTATION
            && !is_attestation_id_tag(p.tag))
        .cloned()
        .collect()
}

/// Forge a keybox-signed attestation chain around the software key's public key (from `sw_leaf_der`,
/// the plain self-signed cert the software KeyMint produced). Mirrors TrickyStoreOSS CertificateGen:
/// full KeyDescription with device IDs, deviceLocked+Verified RootOfTrust, keybox signature.
pub fn forge_cert(sw_leaf_der: &[u8], ctx: &SpoofCtx, security_level: i64, uid: u32) -> Option<Vec<Vec<u8>>> {
    let keybox = keybox()?;
    let out = build_synth_chain(sw_leaf_der, keybox, ctx, &ctx.app_id, security_level)?;
    log::info!("attest_spoof: forged software-backed attestation for uid {} secLvl {} ({} certs)",
        uid, security_level, out.len());
    log::info!("attest_spoof_forge0: {}", hex::encode(&out[0]));
    Some(out)
}

/// Patch the software KeyMint key characteristics so they claim the target security level and the
/// spoofed patch levels (matching the forged attestation cert).
pub fn patch_forge_characteristics(result: &mut KeyCreationResult, ctx: &SpoofCtx, security_level: SecurityLevel) {
    for kc in result.keyCharacteristics.iter() {
        let tags: Vec<i32> = kc.authorizations.iter().map(|a| a.tag.0).collect();
        log::info!("attest_spoof: FORGE-CHARS-BEFORE secLvl={} tags={:?}", kc.securityLevel.0, tags);
    }
    for kc in result.keyCharacteristics.iter_mut() {
        // Promote ONLY the software-KeyMint's hardware-enforceable params (crypto/purpose/patch
        // levels) to the claimed hardware level. Leave the KEYSTORE-enforced entry (holding
        // CREATION_DATETIME) at its level: a genuine TEE/StrongBox key never enforces creation time
        // in hardware, so claiming it at TEE/StrongBox is a tell DroidGuard can catch.
        if kc.securityLevel == SecurityLevel::SOFTWARE {
            kc.securityLevel = security_level;
        } else if kc.securityLevel == SecurityLevel::KEYSTORE {
            // TSOSS buildResponse exports creationDateTime at SOFTWARE (0).
            kc.securityLevel = SecurityLevel::SOFTWARE;
        }
        for p in kc.authorizations.iter_mut() {
            let v = match p.tag {
                Tag::OS_PATCHLEVEL => ctx.os_patch,
                Tag::VENDOR_PATCHLEVEL => ctx.vendor_patch,
                Tag::BOOT_PATCHLEVEL => ctx.boot_patch,
                _ => continue,
            };
            p.value = KeyParameterValue::Integer(v as i32);
        }
    }
}

/// Attestation/keymint version this device reports per security level (matches the real leaves:
/// StrongBox KeyMint is v300, TEE KeyMint is v400).
fn attest_version(security_level: i64) -> i64 {
    if security_level == 2 { 300 } else { 400 }
}

/// Real verified-boot hash from ro.boot.vbmeta.digest (the value the genuine leaf carries), so the
/// forged RootOfTrust bootHash matches what TrickyStoreOSS preserves. Falls back to the stock value.
fn real_boot_hash() -> Vec<u8> {
    // keystore2's SELinux context can't read ro.boot.vbmeta.digest; fall back to this device's
    // genuine verified-boot digest (the value the real KeyMint leaf carries, == TSOSS's).
    rustutils::system_properties::read("ro.boot.vbmeta.digest")
        .ok()
        .flatten()
        .and_then(|s| hex::decode(s.trim()).ok())
        .filter(|v| v.len() == 32)
        .unwrap_or_else(|| hex::decode("d765f3dfed179c55c000113f9be639cca7e1b2e1a495afacf084fb4c9bb13d32").unwrap_or_default())
}

/// Called only AFTER add_required_parameters has checked device-ID permissions on the
/// ORIGINAL request. Retain the challenge, application ID and real hardware key; only
/// authorized target callers can have their requested unique IDs added to the reply.
pub fn keymint_params(params: &[KeyParameter], ctx: Option<&SpoofCtx>) -> Vec<KeyParameter> {
    // Strip the unique device-ID tags (IMEI/serial/MEID) before KeyMint: it rejects them with
    // CANNOT_ATTEST_IDS on this device. synthesize() injects them back into the hacked leaf.
    let substitute_ids = ctx.is_some_and(|c| !c.device_ids.is_empty());
    params.iter().filter(|p| !substitute_ids || !is_unique_device_id(p.tag)).cloned().collect()
}

/// GMS (com.google.android.gms) signing-certificate SHA-256 digests — full history. keystore2's
/// attestation-application-id provider emits only the current signer here, but Google validates the
/// attestation appId against GMS's whole signing history (this is the ONLY field where our hacked
/// leaf differed from a TrickyStoreOSS-forged one, which reads signingCertificateHistory from PM).
const GMS_SIG_DIGESTS: [&str; 3] = [
    "5f2391277b1dbd489000467e4c2fa6af802430080457dce2f618992e9dfb5402",
    "7ce83c1b71f3d572fed04c8d40c5cb10ff75e6d87d9df6fbd53f0468c2905053",
    "f0fd6c5b410f25cb25c3b53346c8972fae30f8ee7411df910480ad6b2d60db83",
];

/// If the request's ATTESTATION_APPLICATION_ID is GMS's, rebuild it with the full signing-cert
/// history so the resulting attestation matches what Google expects (and what TSOSS produces).
pub fn augment_app_id(params: &[KeyParameter]) -> Vec<KeyParameter> {
    let mut out = params.to_vec();
    for p in out.iter_mut() {
        if p.tag == Tag::ATTESTATION_APPLICATION_ID {
            if let KeyParameterValue::Blob(blob) = &p.value {
                if let Some(newid) = rebuild_gms_app_id(blob) {
                    log::info!("attest_spoof: rebuilt GMS appId with full signing history ({} -> {} bytes)", blob.len(), newid.len());
                    p.value = KeyParameterValue::Blob(newid);
                }
            }
        }
    }
    out
}

/// Rebuild an AttestationApplicationId DER, replacing its signatureDigests SET with GMS's full
/// signing history. Returns None (leave untouched) if it is not a GMS appId.
fn rebuild_gms_app_id(app_id: &[u8]) -> Option<Vec<u8>> {
    // AttestationApplicationId ::= SEQUENCE { packageInfos SET, signatureDigests SET OF OCTET_STRING }
    let (_, _, tag, hl, cl) = der_read(app_id, 0)?;
    if tag != 16 { return None; }
    let content = &app_id[hl..hl + cl];
    let (_, _, _, ph, pl) = der_read(content, 0)?;
    let packages = &content[0..ph + pl];
    if !packages.windows(b"com.google.android.gms".len()).any(|w| w == b"com.google.android.gms") {
        return None;
    }
    // DER SET OF requires the elements sorted by their encoding.
    let mut sig_elems: Vec<Vec<u8>> = GMS_SIG_DIGESTS
        .iter()
        .filter_map(|h| hex::decode(h).ok())
        .map(|d| der_octets(&d))
        .collect();
    sig_elems.sort();
    let sigs = der_set(&sig_elems.into_iter().flatten().collect::<Vec<u8>>());
    let mut newseq = Vec::with_capacity(packages.len() + sigs.len());
    newseq.extend_from_slice(packages);
    newseq.extend(sigs);
    Some(der_seq(&newseq))
}

/// Remove attestation-triggering params so KeyMint generates a plain (self-signed) key: no
/// attestation, no RKP. Keeps the key-generation parameters.
pub fn strip_attestation(params: &[KeyParameter]) -> Vec<KeyParameter> {
    // Only strip the challenge: that alone stops keystore2 from requesting an attestation key
    // (no RKP), so KeyMint emits a plain self-signed leaf. Keeping ATTESTATION_APPLICATION_ID and
    // ATTESTATION_ID_* is harmless without a challenge and lets synthesize read them back.
    params.iter().filter(|p| p.tag != Tag::ATTESTATION_CHALLENGE).cloned().collect()
}

/// Observe-only: for a uid listed in OBSERVE_PATH (never modified), dump the REAL KeyMint
/// attestation leaf to logcat so we can compare its structure against our synthesis.
pub fn observe_dump(uid: u32, result: &KeyCreationResult) {
    let Ok(txt) = std::fs::read_to_string(OBSERVE_PATH) else { return; };
    let want: Vec<u32> = txt.lines().filter_map(|l| l.trim().parse::<u32>().ok()).collect();
    if !want.contains(&uid) { return; }
    if let Some(c) = result.certificateChain.first() {
        log::info!("attest_spoof_real0: uid {} {}", uid, hex::encode(&c.encodedCertificate));
    }
}

/// Called after creation_result: replace the self-signed leaf with a keybox-signed synthesized
/// attestation chain. Fail-open.
pub fn synthesize(result: &mut KeyCreationResult, ctx: &SpoofCtx, uid: u32) {
    if result.certificateChain.is_empty() { return; }
    let keybox = match keybox() {
        Some(kb) => kb,
        None => { log::error!("attest_spoof: uid {} no usable keybox", uid); return; }
    };
    match leaf_hack(&result.certificateChain[0].encodedCertificate, keybox, ctx.os_patch, ctx.vendor_patch, ctx.boot_patch, &ctx.device_ids) {
        Some(chain) => {
            log::info!("attest_spoof: leaf-hacked attestation for uid {} ({} certs)", uid, chain.len());
            log::info!("attest_spoof_dump0: {}", hex::encode(&chain[0]));
            log::info!("[DEBUG-funda-pi] returned uid={} requested_id_tags={:?}", uid, ctx.device_ids.iter().map(|(tag, _)| *tag).collect::<Vec<_>>());
            patch_char_patchlevels(result, ctx);
            result.certificateChain =
                chain.into_iter().map(|der| KmCertificate { encodedCertificate: der }).collect();
        }
        None => log::error!("attest_spoof: leaf-hack failed for uid {}", uid),
    }
}

/// Patch OS/VENDOR/BOOT patch levels in the key characteristics so the KeyMetadata.authorizations
/// returned at generateKey (and persisted for getKeyEntry) match the hacked attestation cert.
/// TrickyStoreOSS does the same via CertificateHack.patchAuthorizations.
fn patch_char_patchlevels(result: &mut KeyCreationResult, ctx: &SpoofCtx) {
    for kc in result.keyCharacteristics.iter_mut() {
        for p in kc.authorizations.iter_mut() {
            let v = match p.tag {
                Tag::OS_PATCHLEVEL => ctx.os_patch,
                Tag::VENDOR_PATCHLEVEL => ctx.vendor_patch,
                Tag::BOOT_PATCHLEVEL => ctx.boot_patch,
                _ => continue,
            };
            p.value = KeyParameterValue::Integer(v as i32);
        }
    }
}

/// getKeyEntry hook. Mirrors TrickyStoreOSS Keystore2Interceptor.onPostTransact(getKeyEntry):
/// leaf-hack the retrieved certificate AND patchAuthorizations, so keys read back via
/// KeyStore.getCertificateChain() are patched too — including keys stored before our hook ran
/// (this is why flashing the TSOSS module turns things green immediately).
/// True if `leaf_der`'s issuer matches one of the keybox chain leaf subjects, i.e. we already
/// hacked/forged this cert at generateKey time (so getKeyEntry must serve it unchanged).
fn is_keybox_issued(leaf_der: &[u8], keybox: &Keybox) -> bool {
    let Ok(leaf) = Certificate::from_der(leaf_der) else { return false; };
    let Ok(issuer) = leaf.tbs_certificate.issuer.to_der() else { return false; };
    for entry in [keybox.ec.as_ref(), keybox.rsa.as_ref()].into_iter().flatten() {
        if let Some(c0) = entry.chain_pem.first().and_then(|p| pem_to_der(p)) {
            if let Ok(cert) = Certificate::from_der(&c0) {
                if cert.tbs_certificate.subject.to_der().ok().as_deref() == Some(issuer.as_slice()) {
                    return true;
                }
            }
        }
    }
    false
}

/// getKeyEntry hook: leaf-hack a retrieved attestation cert unless it is already keybox-issued
/// (in which case it was hacked at generateKey and is served unchanged for byte-consistency).
pub fn hack_key_entry(uid: u32, metadata: &mut KeyMetadata) {
    if is_observe(uid) {
        if let Some(c) = metadata.certificate.as_ref() {
            log::info!("attest_spoof_getkey0: uid {} {}", uid, hex::encode(c));
        }
    }
    if !is_target(uid) { return; }
    let Some(leaf) = metadata.certificate.as_ref() else { return; };
    let keybox = match keybox() { Some(kb) => kb, None => return };
    // If this cert was already keybox-issued (we hacked/forged it at generateKey and it is now
    // read back), serve it UNCHANGED. Re-hacking would re-sign the leaf, giving getKeyEntry a
    // different signature than generateKey returned — an inconsistency a genuine key never shows
    // and which DroidGuard can detect. (TrickyStoreOSS caches and serves identical bytes.)
    if is_keybox_issued(leaf, keybox) {
        return;
    }
    let patch = read_patch_levels();
    if let Some(chain) = leaf_hack(leaf, keybox, patch.0, patch.1, patch.1, &[]) {
        metadata.certificate = Some(chain[0].clone());
        let rest: Vec<u8> = chain[1..].iter().flatten().copied().collect();
        metadata.certificateChain = if rest.is_empty() { None } else { Some(rest) };
        patch_authorizations(&mut metadata.authorizations, patch.0, patch.1, patch.1);
        log::info!("attest_spoof: get_key_entry leaf-hacked for uid {}", uid);
    }
}

/// Patch OS/VENDOR/BOOT patch levels in a KeyMetadata authorization list
/// (TrickyStoreOSS CertificateHack.patchAuthorizations).
fn patch_authorizations(auths: &mut [Authorization], os_patch: i64, vendor_patch: i64, boot_patch: i64) {
    for a in auths.iter_mut() {
        let v = match a.keyParameter.tag {
            Tag::OS_PATCHLEVEL => os_patch,
            Tag::VENDOR_PATCHLEVEL => vendor_patch,
            Tag::BOOT_PATCHLEVEL => boot_patch,
            _ => continue,
        };
        a.keyParameter.value = KeyParameterValue::Integer(v as i32);
    }
}

/// True if `uid` is listed in OBSERVE_PATH.
fn is_observe(uid: u32) -> bool {
    match std::fs::read_to_string(OBSERVE_PATH) {
        Ok(t) => t.lines().filter_map(|l| l.trim().parse::<u32>().ok()).any(|u| u == uid),
        Err(_) => false,
    }
}

/// LEAF-HACK (TrickyStoreOSS teeBroken=false path): take KeyMint's REAL attestation leaf, keep
/// everything (version, security level, challenge, appId, device IDs, moduleHash) and rewrite only
/// RootOfTrust[704] (locked+verified) and patch levels [706]/[718]/[719], then re-sign the leaf
/// with the keybox key and splice in the keybox chain.
fn leaf_hack(leaf_der: &[u8], keybox: &Keybox, os_patch: i64, vendor_patch: i64, boot_patch: i64, device_ids: &[(u32, Vec<u8>)]) -> Option<Vec<Vec<u8>>> {
    let leaf = Certificate::from_der(leaf_der).ok()?;
    let is_ec = leaf.tbs_certificate.subject_public_key_info.algorithm.oid == EC_PUBKEY_OID;
    let entry = if is_ec { keybox.ec.as_ref()? } else { keybox.rsa.as_ref()? };
    let chain_der: Vec<Vec<u8>> = entry.chain_pem.iter().filter_map(|p| pem_to_der(p)).collect();
    if chain_der.is_empty() { return None; }
    let issuer_cert = Certificate::from_der(&chain_der[0]).ok()?;

    let exts = leaf.tbs_certificate.extensions.as_ref()?;
    let mut new_exts: Vec<Extension> = Vec::with_capacity(exts.len());
    let mut patched = false;
    for e in exts.iter() {
        if e.extn_id == ATTEST_EXT_OID {
            let new_kd = patch_key_description(e.extn_value.as_bytes(), os_patch, vendor_patch, boot_patch, device_ids)?;
            new_exts.push(Extension {
                extn_id: ATTEST_EXT_OID,
                critical: e.critical,
                extn_value: OctetString::new(new_kd).ok()?,
            });
            patched = true;
        } else {
            new_exts.push(e.clone());
        }
    }
    if !patched { return None; }

    let sig_alg = AlgorithmIdentifierOwned::from_der(
        if is_ec { ALGID_ECDSA_SHA256 } else { ALGID_SHA256_RSA }).ok()?;
    let mut tbs = leaf.tbs_certificate.clone();
    tbs.issuer = issuer_cert.tbs_certificate.subject.clone();
    tbs.signature = sig_alg.clone();
    tbs.extensions = Some(new_exts);

    let tbs_der = tbs.to_der().ok()?;
    let sig = sign_with_keybox(&tbs_der, &entry.private_key_pem, is_ec)?;
    let new_cert = Certificate {
        tbs_certificate: tbs,
        signature_algorithm: sig_alg,
        signature: BitString::from_bytes(&sig).ok()?,
    };
    let mut out = vec![new_cert.to_der().ok()?];
    out.extend(chain_der);
    Some(out)
}

/// Rewrite RootOfTrust[704] and patch levels [706]/[718]/[719] inside a KeyDescription SEQUENCE,
/// leaving every other field byte-identical.
fn patch_key_description(kd: &[u8], os_patch: i64, vendor_patch: i64, boot_patch: i64, device_ids: &[(u32, Vec<u8>)]) -> Option<Vec<u8>> {
    let (_c, _cons, tag, hl, cl) = der_read(kd, 0)?;
    if tag != 16 { return None; }
    let content = &kd[hl..hl + cl];
    let mut elems: Vec<&[u8]> = Vec::new();
    let mut off = 0;
    while off < content.len() {
        let (_, _, _, h, l) = der_read(content, off)?;
        elems.push(&content[off..off + h + l]);
        off += h + l;
    }
    if elems.len() < 8 { return None; }
    let tee_raw = elems[7];
    let (_, _, _, th, tl) = der_read(tee_raw, 0)?;
    let tee_content = &tee_raw[th..th + tl];
    let mut fields: Vec<(u32, Vec<u8>)> = Vec::new();
    let mut o = 0;
    while o < tee_content.len() {
        let (_, _, tagnum, h, l) = der_read(tee_content, o)?;
        let node = &tee_content[o..o + h + l];
        let encoded = match tagnum {
            704 => ctx_explicit(704, &hack_root_of_trust(node)?),
            706 => ctx_explicit(706, &der_int(os_patch)),
            718 => ctx_explicit(718, &der_int(vendor_patch)),
            719 => ctx_explicit(719, &der_int(boot_patch)),
            _ => node.to_vec(),
        };
        if !device_ids.iter().any(|(tag, _)| *tag == tagnum) {
            fields.push((tagnum, encoded));
        }
        o += h + l;
    }
    // TSOSS CertificateGen.buildAttestExtension uses the request's identifier bytes,
    // not system properties, and sorts AuthorizationList by context tag number.
    for (tag, value) in device_ids {
        fields.push((*tag, ctx_explicit(*tag, &der_octets(value))));
    }
    fields.sort_by_key(|(tag, _)| *tag);
    let newtee: Vec<u8> = fields.into_iter().flat_map(|(_, bytes)| bytes).collect();
    let new_tee = der_seq(&newtee);
    let mut kd_new: Vec<u8> = Vec::new();
    for e in elems.iter().take(7) { kd_new.extend_from_slice(e); }
    kd_new.extend(new_tee);
    Some(der_seq(&kd_new))
}

/// From the raw [704] EXPLICIT node, build a RootOfTrust with deviceLocked=TRUE,
/// verifiedBootState=Verified(0), a non-zero verifiedBootKey, and the ORIGINAL verifiedBootHash.
fn hack_root_of_trust(node_704: &[u8]) -> Option<Vec<u8>> {
    let (_, _, _, h, l) = der_read(node_704, 0)?;
    let inner = &node_704[h..h + l];
    let (_, _, _, sh, sl) = der_read(inner, 0)?;
    let rot = &inner[sh..sh + sl];
    let mut els: Vec<&[u8]> = Vec::new();
    let mut o = 0;
    while o < rot.len() {
        let (_, _, _, hh, ll) = der_read(rot, o)?;
        els.push(&rot[o..o + hh + ll]);
        o += hh + ll;
    }
    if els.len() < 4 { return None; }
    let (_, _, _, bh, bl) = der_read(els[3], 0)?;
    let boot_hash = &els[3][bh..bh + bl];
    let mut b: Vec<u8> = Vec::new();
    b.extend(der_octets(&fixed_boot_key()));
    b.extend(der_bool(true));
    b.extend(der_enum(0));
    b.extend(der_octets(boot_hash));
    Some(der_seq(&b))
}

/// Consistent non-zero 32-byte verifiedBootKey (not verified against any registry for the verdict).
fn fixed_boot_key() -> Vec<u8> {
    hex::decode("b596e1a1e87a1c59f31c77ac824442ad69f88280159b0c6b08ce118f17719e38").unwrap_or_default()
}

/// Minimal DER TLV reader: (class, constructed, tagnum, header_len, content_len).
fn der_read(b: &[u8], off: usize) -> Option<(u8, bool, u32, usize, usize)> {
    if off >= b.len() { return None; }
    let first = b[off];
    let class = first >> 6;
    let constructed = first & 0x20 != 0;
    let mut tagnum = (first & 0x1f) as u32;
    let mut p = off + 1;
    if tagnum == 0x1f {
        tagnum = 0;
        loop {
            if p >= b.len() { return None; }
            tagnum = (tagnum << 7) | (b[p] & 0x7f) as u32;
            let more = b[p] & 0x80 != 0;
            p += 1;
            if !more { break; }
        }
    }
    if p >= b.len() { return None; }
    let mut len = (b[p] & 0x7f) as usize;
    let long = b[p] & 0x80 != 0;
    p += 1;
    if long {
        let nb = len;
        len = 0;
        for _ in 0..nb {
            if p >= b.len() { return None; }
            len = (len << 8) | b[p] as usize;
            p += 1;
        }
    }
    Some((class, constructed, tagnum, p - off, len))
}

// Keep the certificate AlgorithmIdentifier and signing digest selected together.
// Values match KeyMint Digest and TSOSS CertificateUtils.digestName (unknown/NONE => SHA-256).
fn forge_signature_algorithm(is_ec: bool, digest: i64) -> Option<(AlgorithmIdentifierOwned, openssl::hash::MessageDigest)> {
    use openssl::hash::MessageDigest;
    let (md, ec_oid, rsa_oid) = match digest {
        2 => (MessageDigest::sha1(), "1.2.840.10045.4.1", "1.2.840.113549.1.1.5"),
        3 => (MessageDigest::sha224(), "1.2.840.10045.4.3.1", "1.2.840.113549.1.1.14"),
        5 => (MessageDigest::sha384(), "1.2.840.10045.4.3.3", "1.2.840.113549.1.1.12"),
        6 => (MessageDigest::sha512(), "1.2.840.10045.4.3.4", "1.2.840.113549.1.1.13"),
        _ => (MessageDigest::sha256(), "1.2.840.10045.4.3.2", "1.2.840.113549.1.1.11"),
    };
    let oid = ObjectIdentifier::new(if is_ec { ec_oid } else { rsa_oid }).ok()?;
    let mut encoded = oid.to_der().ok()?;
    if !is_ec { encoded.extend(der_null()); }
    Some((AlgorithmIdentifierOwned::from_der(&der_seq(&encoded)).ok()?, md))
}

fn build_synth_chain(leaf_der: &[u8], keybox: &Keybox, ctx: &SpoofCtx, app_id: &[u8], security_level: i64) -> Option<Vec<Vec<u8>>> {
    let leaf = Certificate::from_der(leaf_der).ok()?;
    let is_ec = leaf.tbs_certificate.subject_public_key_info.algorithm.oid == EC_PUBKEY_OID;
    let entry = if is_ec { keybox.ec.as_ref()? } else { keybox.rsa.as_ref()? };
    let chain_der: Vec<Vec<u8>> = entry.chain_pem.iter().filter_map(|p| pem_to_der(p)).collect();
    if chain_der.is_empty() { return None; }
    let issuer_cert = Certificate::from_der(&chain_der[0]).ok()?;
    // TSOSS CertificateGen.buildCertificate chooses the first non-NONE requested digest.
    let digest = ctx.digests.iter().copied().find(|d| *d != 0).unwrap_or(4);
    let (sig_alg, md) = forge_signature_algorithm(is_ec, digest)?;

    let key_desc = build_key_description(ctx, app_id, security_level);
    let mut tbs = leaf.tbs_certificate.clone();
    tbs.issuer = issuer_cert.tbs_certificate.subject.clone();
    tbs.signature = sig_alg.clone();
    // Replace extensions with keyUsage(digitalSignature) + our attestation ext (matches TSOSS forge).
    tbs.extensions = Some(vec![
        Extension {
            extn_id: KEY_USAGE_OID,
            critical: true,
            extn_value: OctetString::new(KEY_USAGE_DIGSIG.to_vec()).ok()?,
        },
        Extension {
            extn_id: ATTEST_EXT_OID,
            critical: false,
            extn_value: OctetString::new(key_desc).ok()?,
        },
    ]);

    let tbs_der = tbs.to_der().ok()?;
    let signing_key = openssl::pkey::PKey::private_key_from_pem(entry.private_key_pem.as_bytes()).ok()?;
    let mut signer = openssl::sign::Signer::new(md, &signing_key).ok()?;
    signer.update(&tbs_der).ok()?;
    let sig = signer.sign_to_vec().ok()?;
    let new_cert = Certificate {
        tbs_certificate: tbs,
        signature_algorithm: sig_alg,
        signature: BitString::from_bytes(&sig).ok()?,
    };
    let mut out = vec![new_cert.to_der().ok()?];
    out.extend(chain_der);
    Some(out)
}

/// Build the KeyDescription extension value DER for the forge path, matching TrickyStoreOSS
/// CertificateGen.buildAttestExtension: version/securityLevel per level, softwareEnforced +
/// teeEnforced both sorted by tag, device IDs injected, MODULE_HASH only when attVer >= 400.
fn build_key_description(ctx: &SpoofCtx, app_id: &[u8], security_level: i64) -> Vec<u8> {
    let ver = attest_version(security_level);

    // softwareEnforced (sorted): [701] creationDateTime, [709] appId, [724] moduleHash (v>=400).
    let mut sw: Vec<(u32, Vec<u8>)> = Vec::new();
    sw.push((701, ctx_explicit(701, &der_int(now_millis()))));
    if !app_id.is_empty() {
        sw.push((709, ctx_explicit(709, &der_octets(app_id))));
    }
    if ver >= 400 {
        let module_hash = compute_module_hash();
        if !module_hash.is_empty() {
            sw.push((724, ctx_explicit(724, &der_octets(&module_hash))));
        }
    }
    sw.sort_by_key(|(t, _)| *t);
    let software_enforced = der_seq(&sw.into_iter().flat_map(|(_, b)| b).collect::<Vec<u8>>());

    // teeEnforced (sorted by tag).
    let mut tee: Vec<(u32, Vec<u8>)> = Vec::new();
    let purpose_set = der_set(&ctx.purposes.iter().flat_map(|p| der_int(*p)).collect::<Vec<u8>>());
    tee.push((1, ctx_explicit(1, &purpose_set)));
    tee.push((2, ctx_explicit(2, &der_int(ctx.algorithm))));
    tee.push((3, ctx_explicit(3, &der_int(ctx.key_size))));
    if !ctx.digests.is_empty() {
        let digest_set = der_set(&ctx.digests.iter().flat_map(|d| der_int(*d)).collect::<Vec<u8>>());
        tee.push((5, ctx_explicit(5, &digest_set)));
    }
    if ctx.algorithm == 3 { tee.push((10, ctx_explicit(10, &der_int(ctx.ec_curve)))); }
    tee.push((503, ctx_explicit(503, &der_null())));
    tee.push((702, ctx_explicit(702, &der_int(0))));
    tee.push((704, ctx_explicit(704, &build_root_of_trust())));
    tee.push((705, ctx_explicit(705, &der_int(ctx.os_version))));
    tee.push((706, ctx_explicit(706, &der_int(ctx.os_patch))));
    if !ctx.brand.is_empty() {
        tee.push((710, ctx_explicit(710, &der_octets(&ctx.brand))));
        tee.push((711, ctx_explicit(711, &der_octets(&ctx.device))));
        tee.push((712, ctx_explicit(712, &der_octets(&ctx.product))));
        tee.push((716, ctx_explicit(716, &der_octets(&ctx.manufacturer))));
        tee.push((717, ctx_explicit(717, &der_octets(&ctx.model))));
    }
    // Unique device IDs from the request (serial [713], imei [714], meid [715], second_imei [723]).
    for (tag, value) in &ctx.device_ids {
        tee.push((*tag, ctx_explicit(*tag, &der_octets(value))));
    }
    tee.push((718, ctx_explicit(718, &der_int(ctx.vendor_patch))));
    tee.push((719, ctx_explicit(719, &der_int(ctx.boot_patch))));
    tee.sort_by_key(|(t, _)| *t);
    let tee_enforced = der_seq(&tee.into_iter().flat_map(|(_, b)| b).collect::<Vec<u8>>());

    let mut kd = Vec::new();
    kd.extend(der_int(ver));                       // attestationVersion
    kd.extend(der_enum(security_level as u8));      // attestationSecurityLevel
    kd.extend(der_int(ver));                       // keymintVersion
    kd.extend(der_enum(security_level as u8));      // keymintSecurityLevel
    kd.extend(der_octets(&ctx.challenge));          // attestationChallenge
    kd.extend(der_octets(&[]));                     // uniqueId
    kd.extend(software_enforced);
    kd.extend(tee_enforced);
    der_seq(&kd)
}

fn build_root_of_trust() -> Vec<u8> {
    let mut b = Vec::new();
    b.extend(der_octets(&fixed_boot_key()));
    b.extend(der_bool(true));   // deviceLocked
    b.extend(der_enum(0));      // verifiedBootState = Verified
    b.extend(der_octets(&real_boot_hash()));
    der_seq(&b)
}

/// Read ro.build.version.security_patch ("YYYY-MM-DD") -> (osPatch YYYYMM, ymd YYYYMMDD) so the
/// attestation patch level matches what GMS reports (spoofed or real). Falls back to 2026-08.
fn read_patch_levels() -> (i64, i64) {
    let sp = rustutils::system_properties::read("ro.vendor.build.security_patch")
        .ok()
        .flatten()
        .filter(|s| !s.is_empty())
        .or_else(|| rustutils::system_properties::read("ro.build.version.security_patch").ok().flatten())
        .unwrap_or_default();
    let p: Vec<&str> = sp.split('-').collect();
    if p.len() == 3 {
        if let (Ok(y), Ok(m), Ok(d)) = (p[0].parse::<i64>(), p[1].parse::<i64>(), p[2].parse::<i64>()) {
            return (y * 100 + m, y * 10000 + m * 100 + d);
        }
    }
    (202608, 20260805)
}

/// SHA-256 of keystore2's authoritative ENCODED_MODULE_INFO (the exact value it reports to
/// Google), so the [724] MODULE_HASH matches. Empty if not yet populated.
fn compute_module_hash() -> Vec<u8> {
    match crate::globals::ENCODED_MODULE_INFO.read() {
        Ok(g) => match &*g {
            Some(enc) => sha256(enc),
            // ENCODED_MODULE_INFO isn't populated in keystore2 here; fall back to this build's
            // genuine A16 MODULE_HASH (the value the real KeyMint leaf carries for [724]).
            None => hex::decode("6403170ec053046fa7de79313a6ba4745b4eba2f0f6a28a5a31b64b7d6982aae").unwrap_or_default(),
        },
        Err(_) => Vec::new(),
    }
}

fn sha256(data: &[u8]) -> Vec<u8> {
    use bssl_crypto::digest::Sha256;
    Sha256::hash(data).to_vec()
}

fn now_millis() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis() as i64).unwrap_or(0)
}

// ---- KeyParameter extraction ----
fn get_blob(params: &[KeyParameter], tag: Tag) -> Option<Vec<u8>> {
    params.iter().find(|p| p.tag == tag).and_then(|p| match &p.value {
        KeyParameterValue::Blob(b) => Some(b.clone()),
        _ => None,
    })
}
fn get_int(params: &[KeyParameter], tag: Tag) -> Option<i64> {
    params.iter().find(|p| p.tag == tag).and_then(|p| match &p.value {
        KeyParameterValue::Integer(i) => Some(*i as i64),
        KeyParameterValue::LongInteger(i) => Some(*i),
        _ => None,
    })
}
fn get_algo(params: &[KeyParameter]) -> Option<i64> {
    params.iter().find(|p| p.tag == Tag::ALGORITHM).and_then(|p| match &p.value {
        KeyParameterValue::Algorithm(Algorithm(a)) => Some(*a as i64),
        _ => None,
    })
}
fn get_ec_curve(params: &[KeyParameter]) -> Option<i64> {
    params.iter().find(|p| p.tag == Tag::EC_CURVE).and_then(|p| match &p.value {
        KeyParameterValue::EcCurve(EcCurve(c)) => Some(*c as i64),
        _ => None,
    })
}
fn get_digests(params: &[KeyParameter]) -> Vec<i64> {
    params.iter().filter(|p| p.tag == Tag::DIGEST).filter_map(|p| match &p.value {
        KeyParameterValue::Digest(Digest(d)) => Some(*d as i64),
        _ => None,
    }).collect()
}
fn get_purposes(params: &[KeyParameter]) -> Vec<i64> {
    let v: Vec<i64> = params.iter().filter(|p| p.tag == Tag::PURPOSE).filter_map(|p| match &p.value {
        KeyParameterValue::KeyPurpose(KeyPurpose(k)) => Some(*k as i64),
        _ => None,
    }).collect();
    if v.is_empty() { vec![2] } else { v } // default SIGN
}

// ---- keybox parsing / signing (unchanged) ----
fn load_targets() -> HashSet<u32> {
    let mut set = HashSet::new();
    if let Ok(s) = std::fs::read_to_string(TARGET_PATH) {
        for line in s.lines() {
            let t = line.trim().trim_end_matches('!');
            if t.is_empty() || t.starts_with('#') { continue; }
            if let Ok(uid) = t.parse::<u32>() { set.insert(uid); }
        }
    }
    set
}
fn load_keybox() -> Option<Keybox> {
    let xml = std::fs::read_to_string(KEYBOX_PATH).ok()?;
    let ec = parse_key_entry(&xml, "ecdsa");
    let rsa = parse_key_entry(&xml, "rsa");
    if ec.is_none() && rsa.is_none() { return None; }
    Some(Keybox { ec, rsa })
}
fn parse_key_entry(xml: &str, algo: &str) -> Option<KeyEntry> {
    let open = format!("<Key algorithm=\"{}\"", algo);
    let start = xml.find(&open)?;
    let rest = &xml[start..];
    let end = rest.find("</Key>").map_or(rest.len(), |e| e + "</Key>".len());
    let block = &rest[..end];
    let private_key_pem = extract_all_pem(block, "PRIVATE KEY").into_iter().next()?;
    let chain_pem = extract_all_pem(block, "CERTIFICATE");
    if chain_pem.is_empty() { return None; }
    Some(KeyEntry { private_key_pem, chain_pem })
}
fn extract_all_pem(s: &str, kind: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut hay = s;
    while let Some(bpos) = hay.find("-----BEGIN ") {
        let after = &hay[bpos..];
        let line_end = after.find('\n').unwrap_or(after.len());
        if !after[..line_end].contains(kind) { hay = &after[line_end..]; continue; }
        let Some(epos) = after.find("-----END ") else { break };
        let Some(erel) = after[epos..].find('\n') else { break };
        let cut = epos + erel + 1;
        out.push(after[..cut].trim().to_string());
        hay = &after[cut..];
    }
    out
}
fn pem_to_der(pem: &str) -> Option<Vec<u8>> {
    let start = pem.find("-----BEGIN")?;
    let body_start = pem[start..].find('\n')? + start + 1;
    let end = pem[body_start..].find("-----END")? + body_start;
    b64_decode(&pem[body_start..end])
}
fn b64_decode(s: &str) -> Option<Vec<u8>> {
    fn val(c: u8) -> Option<u32> {
        match c {
            b'A'..=b'Z' => Some((c - b'A') as u32),
            b'a'..=b'z' => Some((c - b'a' + 26) as u32),
            b'0'..=b'9' => Some((c - b'0' + 52) as u32),
            b'+' => Some(62), b'/' => Some(63), _ => None,
        }
    }
    let mut out = Vec::new(); let mut buf = 0u32; let mut bits = 0u32;
    for &c in s.as_bytes() {
        if c == b'=' || c.is_ascii_whitespace() { continue; }
        buf = (buf << 6) | val(c)?; bits += 6;
        if bits >= 8 { bits -= 8; out.push((buf >> bits) as u8); }
    }
    Some(out)
}
fn sign_with_keybox(tbs_der: &[u8], private_key_pem: &str, is_ec: bool) -> Option<Vec<u8>> {
    let key_der = pem_to_der(private_key_pem)?;
    if is_ec {
        let key = bssl_crypto::ecdsa::PrivateKey::<bssl_crypto::ec::P256>::from_der_ec_private_key(&key_der)?;
        Some(key.sign(tbs_der))
    } else {
        let key = bssl_crypto::rsa::PrivateKey::from_der_rsa_private_key(&key_der)?;
        Some(key.sign_pkcs1::<bssl_crypto::digest::Sha256>(tbs_der))
    }
}
fn stock_boot_key() -> Vec<u8> {
    hex::decode("06035f636bdb7f299a94b51c7d5645a913551327ffc5452b00c5830476d3208e").unwrap_or_default()
}
fn stock_boot_hash() -> Vec<u8> {
    hex::decode("5c088fa2f01e035205be6012fde2a372b352cbea2bda689c1914cc37cb1daf7d").unwrap_or_default()
}
// ---- Minimal DER builders (append-style) ----

/// Encode a DER length.
fn der_len(n: usize) -> Vec<u8> {
    if n < 0x80 {
        vec![n as u8]
    } else {
        let mut b = Vec::new();
        let mut v = n;
        while v > 0 { b.push((v & 0xff) as u8); v >>= 8; }
        b.reverse();
        let mut out = vec![0x80 | b.len() as u8];
        out.extend(b);
        out
    }
}

/// tag byte(s) + length + content.
fn tlv(tag: &[u8], content: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(tag.len() + 4 + content.len());
    out.extend_from_slice(tag);
    out.extend(der_len(content.len()));
    out.extend_from_slice(content);
    out
}

fn der_bool(v: bool) -> Vec<u8> { tlv(&[0x01], &[if v {0xff} else {0x00}]) }
fn der_null() -> Vec<u8> { vec![0x05, 0x00] }
fn der_octets(b: &[u8]) -> Vec<u8> { tlv(&[0x04], b) }
fn der_enum(v: u8) -> Vec<u8> { tlv(&[0x0a], &[v]) }
fn der_seq(content: &[u8]) -> Vec<u8> { tlv(&[0x30], content) }
fn der_set(content: &[u8]) -> Vec<u8> { tlv(&[0x31], content) }

/// DER INTEGER for an unsigned i64 (minimal, adds leading 0 if high bit set).
fn der_int(v: i64) -> Vec<u8> {
    if v == 0 { return tlv(&[0x02], &[0x00]); }
    let mut b = Vec::new();
    let mut x = v as u64;
    while x > 0 { b.push((x & 0xff) as u8); x >>= 8; }
    b.reverse();
    if b[0] & 0x80 != 0 { b.insert(0, 0x00); }
    tlv(&[0x02], &b)
}

/// Context-tag bytes for EXPLICIT [tag] constructed (class=0x80|constructed=0x20 => 0xA0 base).
fn ctx_tag(tag: u32) -> Vec<u8> {
    if tag < 0x1f {
        vec![0xA0 | tag as u8]
    } else {
        // high-tag-number form: 0xBF then base-128, high bit set on all but last.
        let mut b = Vec::new();
        let mut v = tag;
        b.push((v & 0x7f) as u8);
        v >>= 7;
        while v > 0 { b.push(((v & 0x7f) as u8) | 0x80); v >>= 7; }
        b.reverse();
        let mut out = vec![0xBF];
        out.extend(b);
        out
    }
}

/// EXPLICIT context-tagged wrapper: [tag] { inner }
fn ctx_explicit(tag: u32, inner: &[u8]) -> Vec<u8> {
    tlv(&ctx_tag(tag), inner)
}
