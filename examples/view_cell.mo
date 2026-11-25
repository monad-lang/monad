/// `Cell`: a linear handle over one `Copy` payload (`init/src/view.mo`).
///
/// The operations are pure linear mutations -- the native writes only the
/// handle it consumes and returns -- so this is an ordinary `let` chain.
/// Every `let p := Cell.get ...` below is the FUSED shape: the initializer
/// is a Cell accessor and the continuation consumes its result immediately,
/// so the compiler lowers them without allocating the `Pair`
/// (`try_compile_view_bind_db`, codegen/src/emit.mo) and the whole program
/// runs in one function. Pass the pair to another def instead and that
/// binding falls back to the boxed path; both compile and agree.
use init::view {Cell}

def main (_args : List String) : IO Unit :=
    let c0 := Cell.new 41 in
    let p := Cell.get c0 in
    match p {
        Pair.pair x c1 =>
            let c2 := Cell.set c1 (I64.add x 1) in
            let p2 := Cell.get c2 in
            match p2 {
                Pair.pair y c3 =>
                    let _ := Cell.free c3 in
                    IO.println (I64.to_string y),
            },
    }
