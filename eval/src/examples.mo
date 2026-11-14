/// The `/try` page's example programs, in one place so the UI
/// (`motes/try_ui/src/app.mo`) and the engine's end-to-end tests
/// (`motes/try_engine/src/tests/pipeline_tests.mo`) cannot drift: the tests
/// evaluate every source below through the real pipeline on every sweep.
///
/// Each source is a complete module for the scratchpad contract: a zero-arg,
/// pure `main`, no `std`/`lib::` imports, no floats, and small enough for the
/// engine's 2,000,000-step / depth-200 budget. `use init::…` is allowed.
pub struct TryExample {
    name : String,
    source : String
}

def example (name : String) (source : String) : TryExample :=
    { name := name, source := source }

pub def try_examples : List TryExample := [
    example "Hello" "def main : String :=\n    \"Hello, \" ++ \"Monad!\"\n",
    example "Arithmetic" "def main : I64 := 6 * 7 + 8 / 2\n",
    example "Lists" "def twice (x : I64) : I64 := x * 2\n\ndef main : List I64 :=\n    List.map twice [1, 2, 3, 4]\n",
    example "Option" "def describe (o : Option I64) : String :=\n    match o {\n        some x => \"got \" ++ I64.to_string x,\n        none => \"nothing\",\n    }\n\ndef main : String := describe (Option.some 42)\n",
    example "Types" "type Shape {\n    circle (r : I64),\n    square (s : I64),\n}\n\ndef area (s : Shape) : I64 :=\n    match s {\n        circle r => 3 * r * r,\n        square x => x * x,\n    }\n\ndef main : I64 := area (Shape.circle 2)\n",
    example "Pipes" "def double (x : I64) : I64 := x * 2\n\ndef inc (x : I64) : I64 := x + 1\n\ndef main : I64 := 5 |> double |> inc\n",
    example "Records" "struct Point {\n    x : I64,\n    y : I64,\n}\n\ndef bump (p : Point) : Point := { p with x := p.x + 1 }\n\ndef main : I64 :=\n    let p : Point := { x := 1, y := 2 } in\n    let q : Point := bump p in\n    q.x\n",
    example "Folds" "use init::foldable {Foldable}\n\ndef main : I64 :=\n    Foldable.foldl (fn (acc : I64) => fn (x : I64) => acc + x) 0 [1, 2, 3, 4]\n",
    example "Recursion" "#[decreasing n]\ndef fact (n : I64) : I64 :=\n    if n == 0\n    then 1\n    else n * fact (n - 1)\n\ndef main : I64 := fact 6\n",
    example "Strings" "def main : String :=\n    String.to_lowercase (\"MONAD \" ++ I64.to_string 42)\n",
    example "Classes" "class Twice A {\n    def twice (a : A) : A\n}\n\ninstance Twice I64 {\n    def twice (a : I64) : I64 := a * 2\n}\n\ndef main : I64 := Twice.twice 21\n"
]
