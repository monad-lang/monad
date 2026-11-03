/// `Cell`: a linear handle over one `Copy` payload (`init/src/view.mo`).
///
/// Every do-bind below is the FUSED shape -- the initializer is a Cell
/// accessor and the continuation consumes its result immediately -- so
/// the compiler lowers them without allocating the IO/Pair boxes
/// (`try_compile_view_bind_db`, lang/src/codegen/emit.mo) and the whole
/// program runs in one function. Pass the pair to another def instead
/// and that bind falls back to the boxed path; both compile and agree.
use init::view {Cell}

def main (_args : List String) : IO Unit := do {
    let c0 <- Cell.new 41;
    let p <- Cell.get c0;
    match p {
        Pair.pair x c1 => do {
            let c2 <- Cell.set c1 (I64.add x 1);
            let p2 <- Cell.get c2;
            match p2 {
                Pair.pair y c3 => do {
                    let _ <- Cell.free c3;
                    IO.println (I64.to_string y)
                },
            }
        },
    }
}
