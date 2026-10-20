/// Checking an editor BUFFER reports exactly what checking the file on
/// disk reports.
///
/// This is the invariant the whole language server rests on. `monad lsp`
/// re-checks its document store on every change through
/// `check_file_cached_from_source` (`lang/module.mo`), which threads the
/// buffer text down to the target module's load instead of reading it
/// from disk. Everything else -- the dependency walk, the scope, the
/// checker -- is the same code the `check` command runs, and this test is
/// what says so out loud rather than by inspection.
///
/// The two loads deliberately do NOT share a cache: they are the disk
/// path and the buffer path as a server and a `check` would run them.
///
/// Slow on purpose: two full closure loads of a temp module (~4s), which
/// is why it lives here and not in `lang/src/tests`.
use std::test {Test.write_fixture}
open IO {println}
use std::process {exec_cmd, process_id}
use std::list {List.length}
use lang::module {
  FileCheckAndCache, FileCheckResult, check_file_cached, check_file_cached_from_source,
  module_info_cache_empty,
}

/// An undefined name, so this is a real diagnostic rather than a clean
/// file -- a clean file would make the assertion below vacuous. (An
/// `x ++ 1` on an `I64` was tried first and checks CLEAN, which made the
/// first version of this probe pass without testing anything.)
def parity_source : String :=
    "def good (x : I64) : I64 := x\ndef bad (x : I64) : I64 := no_such_name x\n"

/// `process_id` in the path, not a fixed name: the sweeps run sharded and
/// a shared /tmp path collides across parallel runs.
def parity_dir : String := "/tmp/monad_lsp_parity_" ++ I64.to_string process_id

/// Typed accessors rather than `f.result.diagnostics` inline. A def whose
/// declared return type differs from the field's type is the documented
/// self-hosted codegen hazard, and the nested spelling would put two
/// different field types in one def.
def parity_result (f : FileCheckAndCache) : FileCheckResult := f.result

def parity_diags (r : FileCheckResult) : List String := r.diagnostics

def string_lists_equal (a : List String) (b : List String) : Bool := match a {
    List.empty => match b {
        List.empty => true,
        List.cons _b_h _b_t => false,
    },
    List.cons a_h a_t => match b {
        List.empty => false,
        List.cons b_h b_t => if String.beq a_h b_h then string_lists_equal a_t b_t else false,
    },
}

#[test]
def test_buffer_check_matches_disk_check : IO Bool := do {
    exec_cmd "mkdir" ["-p", parity_dir];
    let path : String := parity_dir ++ "/parity.mo";
    let _w <- Test.write_fixture (Path.path path) parity_source;
    let disk <- check_file_cached module_info_cache_empty path false;
    let buffer <- check_file_cached_from_source module_info_cache_empty path parity_source false;
    let disk_diags : List String := parity_diags (parity_result disk);
    let buffer_diags : List String := parity_diags (parity_result buffer);
    println ("disk:   " ++ I64.to_string (List.length disk_diags));
    println ("buffer: " ++ I64.to_string (List.length buffer_diags));
    match disk_diags {
        List.empty => do { println "EMPTY DIAGS - probe is vacuous"; return false },
        List.cons d _ => do { println ("first: " ++ d); return string_lists_equal disk_diags buffer_diags },
    }
}
