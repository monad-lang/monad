/// Browser entropy. `WebRandom` is the `Random` class over
/// `crypto.getRandomValues`, so app code can use the standard
/// `Random.bytes`/`Random.token`. The deterministic `SplitMix64` generator
/// lives in `lib::splitmix` (pure, native-testable); seed it from the page
/// clock at mount with `SplitMix64.seed_from_clock`.

use lib::crypto {Crypto.random_bytes}
use lib::clock {Clock.now_ms}
use lib::splitmix {SplitMix64, SplitMix64.seed}
use std::random {Random, RandomError, RandomError.of}

pub struct WebRandom {
    web_random : Unit
}

pub def WebRandom.new : WebRandom := { web_random := unit }

pub instance Random WebRandom {
    def bytes (_r : WebRandom) (n : I64) : IO (Result RandomError (List U8)) := do {
        let res <- Crypto.random_bytes n;
        return (match res {
            Result.ok bs => Result.ok bs,
            Result.err e => Result.err (RandomError.of e),
        })
    }
}

/// Seed a deterministic generator from the wall clock (convenience; a
/// caller that wants a chosen seed uses `SplitMix64.seed` directly).
pub def SplitMix64.seed_from_clock : IO SplitMix64 := do {
    let ms <- Clock.now_ms;
    return (SplitMix64.seed (I64.to_u64 ms))
}
