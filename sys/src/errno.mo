/// How a failed syscall is reported. `no_such_process` is separate from
/// `not_found` because it is the *normal* outcome of racing a process that
/// exits between listing `/proc` and reading its `stat`: a sampler skips it
/// silently, while every other kind is surfaced.
pub type SysErrorKind {
    no_such_process,
    permission_denied,
    not_found,
    invalid_input,
    unsupported,
    other
}

pub struct SysError {
    kind : SysErrorKind,
    errno : I64,
    op : String
}

/// Linux errno values the floor maps; anything else is `other`.
pub def SysError.of_errno (op : String) (errno : I64) : SysError :=
    let k : SysErrorKind :=
        if I64.beq errno 2 then SysErrorKind.not_found
        else if I64.beq errno 3 then SysErrorKind.no_such_process
        else if I64.beq errno 1 then SysErrorKind.permission_denied
        else if I64.beq errno 13 then SysErrorKind.permission_denied
        else if I64.beq errno 22 then SysErrorKind.invalid_input
        else if I64.beq errno 38 then SysErrorKind.unsupported
        else SysErrorKind.other in
    let e : SysError := { kind := k, errno := errno, op := op } in
    e

pub def SysError.is_missing (e : SysError) : Bool :=
    match e.kind {
        SysErrorKind.no_such_process => true,
        SysErrorKind.not_found => true,
        SysErrorKind.permission_denied => false,
        SysErrorKind.invalid_input => false,
        SysErrorKind.unsupported => false,
        SysErrorKind.other => false
    }
