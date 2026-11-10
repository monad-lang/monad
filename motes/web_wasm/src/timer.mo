/// One-shot timers for Oak's `Command.after`. The host returns an id in the
/// top bit (the space `Handler.id` masks away); the wasm runtime keeps the
/// message and resolves the id when the host calls `oak_dispatch_event(id)`.

use lib::ffi {timer_after_raw}

pub def Timer.base : I64 := 0x80000000i64

pub def Timer.is_id (id : U32) : Bool :=
    U32.beq (U32.and id (I64.to_u32 Timer.base)) (I64.to_u32 Timer.base)

pub def Timer.after (ms : I64) : IO I64 :=
    IO.mk (timer_after_raw (if I64.lt ms 0i64 then 0i64 else ms))
