/// The one OpenSSL symbol this mote calls: `int RAND_bytes(unsigned char
/// *buf, int num)`.
///
/// Declarative `#[extern "c"]`, the `motes/tls/src/ffi.mo` convention: the
/// symbol binds by NAME at link time and `motes/crypto`'s `[link]` table
/// supplies `-lcrypto`. The Rust host has no C bridge and warns that it is
/// ignoring this, so every test that forces it is compiled-only.
///
/// `RawIO I32` because it writes through `buf`. The only pointer a caller
/// may pass is `ByteBuf.ptr buf`, and the only length is that buffer's own
/// (clamped) allocation size — see `random.mo`. There is no way to hand
/// this an arbitrary address or an unchecked count.
///
/// Returns 1 on success, 0 if the RNG state is unusable.
#[extern "c"]
def RAND_bytes (buf : Ptr) (num : I32) : RawIO I32
