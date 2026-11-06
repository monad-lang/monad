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
