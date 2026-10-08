/// tls's link-libraries check — `-lssl` is opt-in, and this pins it.
///
/// tls.md Design 1: a program that does not depend on `motes/tls` must
/// link no `-lssl`. The mechanism is `collect_link_libs` unioning each
/// loaded manifest's `[link] libs` over the dependency closure, so both
/// halves are checked at that level: a fixture mote with no tls
/// dependency yields no "ssl", and the REAL tls manifest yields both
/// "ssl" and "crypto" (an unparseable manifest silently yields nothing —
/// the failure mode motes/moose/mote.toml's comment warns about — so the
/// positive half is a pin, not a tautology).
///
/// It lives HERE, not in motes/tls, because reaching into the compiler
/// (`lang::module`) is what this mote exists for and declares as a
/// dependency; `validate_declared_deps` would otherwise demand a
/// `[dependencies.lang]` on the tls mote, and every tls consumer (moose)
/// would inherit the whole compiler in its closure. Loading
/// `motes/tls/src/ffi.mo` by path needs no declared dependency — the
/// manifest walk that finds its `[link]` entry is a filesystem scan.
///
/// No network and no extern is forced here, so unlike tls's
/// `e2e_tests.mo` these run ungated, under any runner that can load
/// modules (they pass under the Rust host too).

use std::process {process_id}
use lang::module {collect_link_libs, get_loaded_all, load_file_modules}

/// The fixture: a module with no externs, in a mote whose manifest
/// declares no libraries — the shape of every program that does not use
/// TLS.
def no_tls_fixture_source : String := r#"
def value : I64 := 7
"#

def no_tls_fixture_manifest : String := r#"
[mote]
name = "no_tls_probe"
version = "0.1.0"
edition = "2026"
"#

/// `List` has no BEq instance in scope here, so the membership scan is
/// spelled out (`String.beq` per element).
#[terminating]
def lib_listed (name : String) (libs : List String) : Bool :=
  match libs {
    List.empty => false,
    List.cons h t => Bool.or (String.beq h name) (lib_listed name t)
  }

/// A program outside the tls mote links no `-lssl`: Design 1's promise,
/// checked where it is kept (`collect_link_libs` over the loaded
/// closure), not where it is observed (a linker invocation).
#[test]
def test_link_libs_plain_program_gets_no_ssl : IO Bool := do {
  let dir := "/tmp/monad_tls_libs_" ++ I64.to_string process_id;
  exec_cmd "mkdir" ["-p", dir ++ "/src"];
  IO.write_file (Path.path (dir ++ "/mote.toml")) no_tls_fixture_manifest;
  IO.write_file (Path.path (dir ++ "/src/probe.mo")) no_tls_fixture_source;
  let loaded <- load_file_modules (dir ++ "/src/probe.mo") false;
  match loaded {
    Result.err _ => return false,
    Result.ok l => do {
      let libs <- collect_link_libs (get_loaded_all l);
      return (Bool.not (lib_listed "ssl" libs))
    }
  }
}

/// The tls mote's own manifest yields both of OpenSSL's libraries — the
/// positive control without which the test above could pass because
/// manifest reading broke entirely.
#[test]
def test_link_libs_tls_manifest_yields_ssl_and_crypto : IO Bool := do {
  let loaded <- load_file_modules "motes/tls/src/ffi.mo" false;
  match loaded {
    Result.err _ => return false,
    Result.ok l => do {
      let libs <- collect_link_libs (get_loaded_all l);
      return (Bool.and (lib_listed "ssl" libs) (lib_listed "crypto" libs))
    }
  }
}