/// `String`-keyed `HashMap` helpers, monomorphic on purpose.
///
/// A leaf module: it imports `std.map` and nothing else. That is the whole
/// reason it exists separately from `lang/codegen/util.mo`, which is where
/// these lived. `util.mo` imports `lang.codegen.ir` (for `LLVMInstruction`
/// and friends), so `ir.mo` cannot import `util.mo` back -- and `ir.mo`
/// needs a string map of its own for the per-function debug-metadata table
/// (`find_dbg_refs` was a linear assoc-list scan, O(F^2) module-wide).
/// Extracting them here is what lets both files use one implementation
/// instead of two, which duplicate top-level names would make a real
/// collision hazard (AGENTS.md item 18), not just a tidiness question.
///
/// `util.mo` re-exports them with `pub use`, so every existing
/// `use lang.codegen.util {str_map_*}` importer is unaffected.
///
/// These bypass `Map`'s abstract typeclass dispatch (`Map.insert`/
/// `Map.lookup`, the `[Hashable K, BOrd K] Map HashMap` instance,
/// `std/map.mo`) in favor of `HashMap.bucket_of`/`get_bucket`/`set_bucket`/
/// `bucket_insert_str`/`bucket_lookup_str` called directly with plain
/// `String.hash` (concrete native, no class-method resolution
/// at all). Mirrors `lang/scope.mo`'s own `modpath_map_*` helpers, which
/// document why: calling through `Map`'s generic dispatch resolves
/// `Hashable.hash`/`BOrd.lt`/`BOrd.gt` as abstract class-method references
/// INSIDE `HashMap`'s own generic `[K, V]`-parameterized body, and
/// AGENTS.md's documented evaluator limitation ("`resolve_class_method_
/// instance` picks the FIRST REGISTERED instance", not a type-directed
/// lookup) means these can silently resolve to the WRONG instance whenever
/// invoked from deep within an already-polymorphic call chain -- confirmed
/// as a real, live bug for `ScopeData.def_refs`/`inductives`, not merely
/// theoretical. `String.hash`/`String.beq` need no dispatch at all, so this
/// sidesteps the whole class of risk rather than hoping it does not fire.
use std.map {}

#[partial]
def str_map_empty {V : Type} : HashMap String V := HashMap.map HashMap.empty_buckets

#[partial]
def str_map_insert {V : Type} (key : String) (val : V) (m : HashMap String V) : HashMap String V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            let new_bucket := HashMap.bucket_insert_str key val bucket in
            HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

#[partial]
def str_map_lookup {V : Type} (key : String) (m : HashMap String V) : Option V :=
    match m {
        HashMap.map buckets =>
            let idx := HashMap.bucket_of (String.hash key) in
            let bucket := HashMap.get_bucket buckets idx in
            HashMap.bucket_lookup_str key bucket
    }
