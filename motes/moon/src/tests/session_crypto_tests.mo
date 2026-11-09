/// CSPRNG session ids through `motes/crypto` (OpenSSL RAND_bytes).

use std::test {}
use moon::session {
    SessionConfig, SessionConfig.default, SessionStore, SessionStore.new_id_checked,
    SessionStore.new_with,
}
use moon::session_crypto {SessionConfig.with_crypto_ids}

// ── CSPRNG ids from motes/crypto ─────────────────────────────────────────

def check_crypto_ids (st : SessionStore) : IO Bool := do {
    let a <- SessionStore.new_id_checked st;
    let b <- SessionStore.new_id_checked st;
    match a {
        Result.err _ => IO.pure false,
        Result.ok ida =>
            match b {
                Result.err _ => IO.pure false,
                Result.ok idb =>
                    IO.pure (Bool.and (I64.beq (String.length ida) 43i64)
                        (Bool.not (String.beq ida idb)))
            }
    }
}

#[test]
def test_crypto_session_ids_are_random : IO Bool := do {
    let cfg := SessionConfig.with_crypto_ids (SessionConfig.default "sid" 3600i64);
    let st_res <- SessionStore.new_with cfg;
    match st_res {
        Result.err _ => IO.pure false,
        Result.ok st => check_crypto_ids st
    }
}
