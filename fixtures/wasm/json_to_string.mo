// `Json.to_string` under the web profile. Its `float` arm reaches
// `F64.to_string`, whose web implementation used to be gated off with the
// freestanding profile's missing libc float formatting -- so even an
// integer/string document failed the reachable-native gate
// (`2026-10-20-json-to-string-web-gate`). The document deliberately keeps
// one float arm in the type, and two float values in the data (an exact
// one and a repeating one, so the shortest-round-trip search is
// exercised), and native/wasi/web must agree byte for byte:
//  [1,"a",0.5,0.3333333333333333]

#![mote { name := "json_to_string", deps := [json] }]

use json::json {Json}

def main (args : List String) : IO I64 := do {
    let doc : Json := Json.make_array
        [ Json.make_num_int 1i64,
          Json.make_str "a",
          Json.make_num_float 0.5,
          Json.make_num_float (F64.div 1.0 3.0) ];
    let _ <- IO.println (Json.to_string doc);
    return 0
}
