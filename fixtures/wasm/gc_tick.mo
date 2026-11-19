// The web collector under a frame loop (`wasm/web/smoke/gc_smoke.mjs`).
//
// `gc_mount` keeps a 2000-element list in a `Ref` through `Keep`. Every
// `gc_tick` replaces it with a copy shifted by one, so the old list is
// garbage, and builds ~3 MB of throwaway strings and cons cells. It logs
// the state's sum, which the harness checks exactly: a collector that
// frees a live cell corrupts the sum, and one that frees nothing grows
// linear memory without bound.

#![mote { name := "gc_tick", deps := [web_wasm] }]

use std::ref {Ref, Ref.get, Ref.new, Ref.set}
use web_wasm::keep {Keep.load, Keep.save}
use web_wasm::console {Console.log}

def STATE_LEN : I64 := 2000

#[terminating]
def build (i : I64) (n : I64) (acc : List I64) : List I64 :=
    if i == n then acc else build (i + 1) n (List.cons (n - 1 - i) acc)

def shift (xs : List I64) : List I64 := List.map (fn (x : I64) => x + 1) xs

def sum_go (xs : List I64) (acc : I64) : I64 := match xs {
    List.empty => acc,
    List.cons x rest => sum_go rest (acc + x),
}

#[terminating]
def garbage (i : I64) (n : I64) (acc : List String) : List String :=
    if i == n then acc else garbage (i + 1) n (List.cons (I64.to_string (i * 7919)) acc)

def total_length (xs : List String) (acc : I64) : I64 := match xs {
    List.empty => acc,
    List.cons s rest => total_length rest (acc + String.length s),
}

#[export "c"]
def gc_mount : IO Unit := do {
    let r <- Ref.new (build 0 STATE_LEN List.empty);
    Keep.save r
}

#[export "c"]
def gc_tick : IO Unit := do {
    let r : Ref (List I64) <- Keep.load;
    let xs <- Ref.get r;
    let next : List I64 := shift xs;
    let waste : I64 := total_length (garbage 0 50000 List.empty) 0;
    let _ <- Ref.set r next;
    let now <- Ref.get r;
    Console.log (I64.to_string (sum_go now 0) ++ " " ++ I64.to_string waste)
}
