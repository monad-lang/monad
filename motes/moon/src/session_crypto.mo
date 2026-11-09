/// Opt-in CSPRNG session ids through `motes/crypto` (OpenSSL
/// `RAND_bytes`).
///
/// `moon` does not re-export this module from `lib.mo`: importing it is the
/// statement that the program wants libcrypto linked. The dependency is
/// declared in `moon/mote.toml`, but the linker only sees the modules a
/// program actually loads, so `use moon` alone does not pull OpenSSL in.
///
/// `Random.token` is `[Random R]`-constrained; it is called from a concrete
/// top-level def, not from a lambda stored in the config (a constrained call
/// inside a lambda crashes the compiled backend).

use std::random {Random, Random.token, RandomError}
use crypto::random {CryptoRandom.new}
use lib::session {SessionConfig}

def SessionConfig.crypto_token (_ : Unit) : IO (Result String String) := do {
    let r <- Random.token CryptoRandom.new 32i64;
    match r {
        Result.ok token => IO.pure (Result.ok token),
        Result.err e => IO.pure (Result.err (RandomError.to_string e))
    }
}

/// Copy `cfg` with a 32-byte CSPRNG id source.
pub def SessionConfig.with_crypto_ids (cfg : SessionConfig) : SessionConfig :=
    let cfg2 : SessionConfig :=
        { cfg with next_id := Option.some SessionConfig.crypto_token } in
    cfg2
