// The sound vocabulary and its pure helpers. These never touch an
// `AudioContext`, so they run on every target -- which is the property that
// lets an `update` returning `Command.beep` be tested without a browser.

use lib::sound {MediaCmd, SoundFx, Wave, SoundFx.is_silence, Wave.code}

#[test]
def test_wave_codes_are_the_host_table_order : Bool :=
    I64.beq (Wave.code Wave.sine) 0i64
        && I64.beq (Wave.code Wave.square) 1i64
        && I64.beq (Wave.code Wave.sawtooth) 2i64
        && I64.beq (Wave.code Wave.triangle) 3i64

#[test]
def test_silence_is_the_only_silent_fx : Bool :=
    SoundFx.is_silence SoundFx.silence
        && Bool.not (SoundFx.is_silence (SoundFx.beep Wave.sine 440.0 0.5 100i64))
        && Bool.not (SoundFx.is_silence (SoundFx.hit 0.5 50i64 0.0))
        && Bool.not (SoundFx.is_silence (SoundFx.file "/a.ogg" 0.5))

/// A `SoundFx` is pure DATA: it can be built, compared by shape and stored in
/// a model without an effect running. Reading a field out of it is the check.
#[test]
def test_fx_carries_its_parameters : Bool :=
    match SoundFx.beep Wave.triangle 220.0 0.25 90i64 {
        SoundFx.beep wave freq gain duration_ms =>
            I64.beq (Wave.code wave) 3i64
                && F64.beq freq 220.0
                && F64.beq gain 0.25
                && I64.beq duration_ms 90i64,
        _ => false,
    }

#[test]
def test_hit_carries_its_parameters : Bool :=
    match SoundFx.hit 0.4 30i64 1200.0 {
        SoundFx.hit gain duration_ms lowpass_hz =>
            F64.beq gain 0.4 && I64.beq duration_ms 30i64 && F64.beq lowpass_hz 1200.0,
        _ => false,
    }

#[test]
def test_file_carries_its_url : Bool :=
    match SoundFx.file "/sfx/hit.ogg" 0.75 {
        SoundFx.file url gain => String.beq url "/sfx/hit.ogg" && F64.beq gain 0.75,
        _ => false,
    }

/// A `MediaCmd` addresses an element by selector and carries its argument;
/// nothing about it needs the DOM to be well-formed.
#[test]
def test_media_seek_carries_ms : Bool :=
    match MediaCmd.seek "#player" 42500i64 {
        MediaCmd.seek selector ms => String.beq selector "#player" && I64.beq ms 42500i64,
        _ => false,
    }

#[test]
def test_media_volume_is_fractional : Bool :=
    match MediaCmd.volume "#music" 0.3 {
        MediaCmd.volume selector volume => String.beq selector "#music" && F64.beq volume 0.3,
        _ => false,
    }
