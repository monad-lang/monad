/// The errno mapping is the contract every caller depends on:
/// `no_such_process` must be skippable, the rest must not.

use sys::errno {SysError, SysError.is_missing, SysError.of_errno, SysErrorKind}

#[test]
def test_errno_kinds : Bool :=
    SysError.is_missing (SysError.of_errno "stat" 3)
    && SysError.is_missing (SysError.of_errno "stat" 2)
    && Bool.not (SysError.is_missing (SysError.of_errno "stat" 13))

#[test]
def test_errno_keeps_the_number : Bool :=
    match SysError.of_errno "kill" 1 {
        { errno, op, kind } => match kind {
            SysErrorKind.permission_denied => I64.beq errno 1 && String.beq op "kill",
            _ => false,
        },
    }
