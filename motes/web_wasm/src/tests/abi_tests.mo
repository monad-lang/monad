/// ABI drift guard: every import the loader maps must have a `host.<name>`
/// implementation in `wasm/web/web_runtime.js`.
///
/// The generated `web.js` only forwards names, so a missing host function is
/// a runtime `TypeError` at the first call. This test turns that into a
/// suite failure. Runs from the repository root (where both `monad test` and
/// the Rust host run tests).

use lib::web_abi {WebAbi, WebImport}

#[test]
def test_every_import_has_a_host_function : IO Bool := do {
  let r <- IO.read_file (Path.path "wasm/web/web_runtime.js");
  match r {
    Result.err _ => return false,
    Result.ok text => return (all_present (imports_of WebAbi.default) text)
  }
}

def imports_of (abi : WebAbi) : List WebImport := abi.imports

#[terminating]
def all_present (imports : List WebImport) (text : String) : Bool :=
  match imports {
    List.empty => true,
    List.cons imp rest =>
      if String.contains text (String.concat imp.name "(")
      then all_present rest text
      else false
  }
