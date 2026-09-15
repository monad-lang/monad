// ffi_example / ffi_test — the FFI codegen as a program a human runs and
// eyeballs: `monad run motes/ffi_example/src/ffi_test.mo` compiles it,
// links it, and the produced binary prints what the C side printed back.
// It is NOT the automated test -- `ffi_codegen_e2e_test.mo` and
// `ffi_link_test.mo` in this directory are that.
//
// Two blockers used to stand between this file and running, and both are
// gone:
//
//   * `native f64_to_string` (needed by `number::F64.to_string`) was not
//     wired into the native backend -- now it is (`natives.mo`'s table,
//     `runtime/src/runtime.c`).
//   * `#[extern "c"]` with no explicit `link_name` emitted a
//     module-qualified C symbol (`ffi_example::sin`), which no linker
//     could resolve -- `unqualify_def_name` on the defaulted name fixed
//     that.
//
// `sin` also needs `-lm`, and gets it from this mote's own `[link] libs`,
// on the `run` path and (link libraries travelling with the loaded set)
// on `monad test` too.

use lib::libc {puts, strlen, sin}

def main : I64 :=
  let ignored := puts "eval works\n" in
  let n := strlen "hello" in
  let ignored2 := puts (String.concat "strlen=" (I64.to_string n)) in
  let sine := sin 0.0 in
  let ignored3 := puts (String.concat "sin(0.0)=" (F64.to_string sine)) in
  let ignored4 := puts "done\n" in
  0