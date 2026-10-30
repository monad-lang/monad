/// The OpenSSL symbols `motes/crypto` calls.
///
/// Declarative `#[extern "c"]`, the `motes/tls/src/ffi.mo` convention: the
/// symbol binds by NAME at link time and `motes/crypto`'s `[link]` table
/// supplies `-lcrypto`. The Rust host has no C bridge and warns that it is
/// ignoring these, so every test that forces one is compiled-only.
///
/// The `RawIO I32` annotations are not decoration: `EVP_DigestVerifyInit`,
/// `EVP_DigestVerify` and the `set1` calls all mutate the handle they are
/// given, and every allocating call writes through a handle the caller must
/// eventually release.
///
/// Memory-safety boundary (AGENTS.md): every byte argument is a
/// `ByteBuf.ptr` with that same buffer's `ByteBuf.length`; there is no
/// `I64 -> Ptr`, no pointer arithmetic, and no generic load/store. The
/// `Ptr` handles below are package-private and never appear in a public
/// signature.

// ── the CSPRNG ───────────────────────────────────────────────────────────

#[extern "c"]
def RAND_bytes (buf : Ptr) (num : I32) : RawIO I32

// ── BIGNUM ───────────────────────────────────────────────────────────────

/// Read `len` big-endian bytes into a fresh BIGNUM. `ret` is NULL (unused).
#[extern "c"]
def BN_bin2bn (buf : Ptr) (len : I32) (ret : Ptr) : RawIO Ptr

#[extern "c"]
def BN_free (bn : Ptr) : RawIO Unit

// ── RSA ──────────────────────────────────────────────────────────────────

#[extern "c"]
def RSA_new : RawIO Ptr

/// Install `n`, `e` (and a NULL private exponent) on `rsa`. On success the
/// RSA object owns the BIGNUMs; on failure the caller still owns them.
#[extern "c"]
def RSA_set0_key (rsa : Ptr) (n : Ptr) (e : Ptr) (d : Ptr) : RawIO I32

#[extern "c"]
def RSA_free (rsa : Ptr) : RawIO Unit

// ── P-256 ────────────────────────────────────────────────────────────────

#[extern "c"]
def EC_KEY_new_by_curve_name (nid : I32) : RawIO Ptr

#[extern "c"]
def EC_KEY_free (key : Ptr) : RawIO Unit

/// Borrowed, not owned: the group lives inside the EC_KEY.
#[extern "c"]
def EC_KEY_get0_group (key : Ptr) : Ptr

#[extern "c"]
def EC_POINT_new (group : Ptr) : RawIO Ptr

#[extern "c"]
def EC_POINT_free (point : Ptr) : RawIO Unit

/// Decode one uncompressed point (`0x04 || x || y`). `ctx` is NULL.
#[extern "c"]
def EC_POINT_oct2point
  (group : Ptr) (point : Ptr) (buf : Ptr) (len : I64) (ctx : Ptr) : RawIO I32

/// The key copies the point, so the caller still frees its own `point`.
#[extern "c"]
def EC_KEY_set_public_key (key : Ptr) (point : Ptr) : RawIO I32

// ── EVP keys ─────────────────────────────────────────────────────────────

#[extern "c"]
def EVP_PKEY_new : RawIO Ptr

#[extern "c"]
def EVP_PKEY_free (pkey : Ptr) : RawIO Unit

#[extern "c"]
def EVP_PKEY_set1_RSA (pkey : Ptr) (rsa : Ptr) : RawIO I32

#[extern "c"]
def EVP_PKEY_set1_EC_KEY (pkey : Ptr) (ec : Ptr) : RawIO I32

/// Ed25519 takes its public key as 32 raw bytes; the engine argument is NULL.
#[extern "c"]
def EVP_PKEY_new_raw_public_key
  (typ : I32) (engine : Ptr) (key : Ptr) (len : I64) : RawIO Ptr

// ── verification ─────────────────────────────────────────────────────────

#[extern "c"]
def EVP_MD_CTX_new : RawIO Ptr

#[extern "c"]
def EVP_MD_CTX_free (ctx : Ptr) : RawIO Unit

/// SHA-256 for RS256 and ES256; EdDSA passes a NULL digest.
#[extern "c"]
def EVP_sha256 : Ptr

/// `pctx` and `engine` are NULL.
#[extern "c"]
def EVP_DigestVerifyInit
  (ctx : Ptr) (pctx : Ptr) (md : Ptr) (engine : Ptr) (pkey : Ptr) : RawIO I32

/// 1 valid, 0 invalid, < 0 on a verification error.
#[extern "c"]
def EVP_DigestVerify
  (ctx : Ptr) (sig : Ptr) (sig_len : I64) (msg : Ptr) (msg_len : I64) : RawIO I32
