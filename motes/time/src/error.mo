/// `TimeError` construction and accessors.
///
/// `TimeError` itself is declared in `types.mo` (a derive-bearing,
/// body-free file); the functions that build and inspect it live here.

use lib::types {TimeError, TimeErrorKind}

/// Build a `TimeError` from its kind and message.
pub def TimeError.of (kind : TimeErrorKind) (message : String) : TimeError :=
    let e : TimeError := { kind := kind, message := message } in
    e

/// The machine-branchable kind of a rejected operation.
pub def TimeError.kind (e : TimeError) : TimeErrorKind :=
    match e { mk k _ => k }

/// The human-readable message of a rejected operation.
pub def TimeError.message (e : TimeError) : String :=
    match e { mk _ m => m }
