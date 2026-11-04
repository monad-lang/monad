/// The re-export hubs are ambient, and nothing special makes them so.
///
/// `init/src/lib.mo` re-exports `id`, `io`, `number`, `math`, `string` and
/// `list` with `pub use lib::X {*}`, and `std/src/lib.mo` re-exports
/// `path`, `io` and `process`. `prelude`, `init` and `std` are the ambient
/// trio (`is_ambient_mote`, `lang/src/module.mo`), so a `{*}` re-export out
/// of an ambient mote puts that module's qualified names -- types, dotted
/// defs, and the instances it declares -- into every file's scope with no
/// `use` at all.
///
/// That is the whole rule, and these tests pin it by compiling sources that
/// contain NO `use` line whatsoever: a file needing `IO`, its `Monad`
/// instance, or `Path` must reach all three anyway. The corpus used to
/// spell the imports out (`use init::io {IO}` in 60 files, `use init::io
/// {}` in more) for no reason beyond not trusting that, which also meant a
/// regression making the hubs conditional on the spelling would have been
/// invisible -- every file that would have failed carried the line.
open IO {println}
use codegen::test::e2e_harness {compile_source_run_expect}

/// `IO` (the type), `IO.pure` (a dotted def), a `do` block's implicit
/// `Monad IO`, and the `init` hub's other re-exports -- `String`, `I64`,
/// `Option`, and a bare type annotation -- with no `use` anywhere.
#[test]
def test_init_hub_is_ambient : IO Bool :=
    let source := r#"def main (args : List String) : IO I64 := do {
    let a <- IO.pure 41;
    let s := String.concat "n=" (I64.to_string a);
    let o : Option I64 := Option.some (String.length s);
    return (Option.get_or_default 0 o)
}
"# in
    compile_source_run_expect source "test_init_hub_is_ambient" 4

/// The `std` hub the same way: `Path` and `Path.to_string` are reachable
/// with no import. The two halves are separate hubs (`IO.pure` above is
/// `init`'s; `Path` here is `std`'s), so this is not the previous test
/// wearing a different type.
#[test]
def test_std_hub_is_ambient : IO Bool :=
    let source := r#"def label (p : Path) : String := Path.to_string p

def main (args : List String) : IO I64 := do {
    let s <- IO.pure (label (Path.path "abcd"));
    return (String.length s)
}
"# in
    compile_source_run_expect source "test_std_hub_is_ambient" 4
