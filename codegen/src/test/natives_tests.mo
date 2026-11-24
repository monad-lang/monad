/// Tests moved out of `codegen::natives` so the production module stays readable.

use llvm::strmap {str_map_empty, str_map_insert, str_map_lookup}
use lang::types {AttrArg, Attribute, id, id_eq}
use llvm::ir {LLVMDeclaration, NativeOp}
use llvm::target {TargetKind}
use lib::symbols {
    extract_base_name, replace_dots_with_underscores, symbol_identifier,
}
use lang::name_text {unqualify_def_name}
use lib::util {}
use std::map {HashMap}
use lib::natives {NativeAvailability, native_target_availability}

#[test]
def test_wasm_gates_posix_only_natives : Bool :=
    match native_target_availability TargetKind.wasi "term_ctl" {
        NativeAvailability.unavailable _ => true,
        NativeAvailability.available => false,
    }
        && match native_target_availability TargetKind.web "fork_io" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.wasi "tcp_connect_timeout" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.web "poll_fiber" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.wasi "channel_take" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }

#[test]
def test_wasm_keeps_console_and_arithmetic : Bool :=
    match native_target_availability TargetKind.wasi "stream_write" {
        NativeAvailability.available => true,
        NativeAvailability.unavailable _ => false,
    }
        && match native_target_availability TargetKind.web "print_str" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.native "term_ctl" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }

#[test]
def test_web_gates_float_formatting : Bool :=
    // The web profile formats floats through the JS host (platform_web.c),
    // so only the decimal PARSER (`f64_of_string`, strtod) stays gated there.
    match native_target_availability TargetKind.web "f64_to_string" {
        NativeAvailability.available => true,
        NativeAvailability.unavailable _ => false,
    }
        && match native_target_availability TargetKind.web "f64_of_string" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.wasi "f64_to_string" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }

/// The Windows target is CORE ONLY, and this is the half of that claim that
/// matters most: every concurrency primitive is refused, because each one is
/// an OS thread on POSIX with no honest single-threaded substitute.
#[test]
def test_windows_gates_threads_processes_and_sockets : Bool :=
    match native_target_availability TargetKind.windows "fork_io" {
        NativeAvailability.unavailable _ => true,
        NativeAvailability.available => false,
    }
        && match native_target_availability TargetKind.windows "channel_put" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.windows "proc_spawn" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.windows "tcp_connect_timeout" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.windows "stream_open" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }
        && match native_target_availability TargetKind.windows "inotify_init" {
            NativeAvailability.unavailable _ => true,
            NativeAvailability.available => false,
        }

/// ...and the half that makes the target useful. Everything a console program
/// over the three standard descriptors needs stays available, INCLUDING the
/// sys floor and `sleep_io` -- both of which the wasm profiles refuse, so this
/// also pins the list as deliberately NOT an alias of `wasm_os_only_natives`.
#[test]
def test_windows_keeps_the_console_clock_and_sys_floor : Bool :=
    match native_target_availability TargetKind.windows "print_str" {
        NativeAvailability.available => true,
        NativeAvailability.unavailable _ => false,
    }
        && match native_target_availability TargetKind.windows "read_stdin_exact" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.windows "stream_write" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.windows "clock_now" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.windows "sleep_io" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.windows "sys_int" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
        && match native_target_availability TargetKind.windows "sys_dir_open" {
            NativeAvailability.available => true,
            NativeAvailability.unavailable _ => false,
        }
