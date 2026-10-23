/// IO body helpers: draining streams, byte caps, and chunked wire output.

use std::bytebuf {ByteBuf, ByteBuf.length, ByteBuf.to_list}
use std::ref {Ref, Ref.get, Ref.new, Ref.set, Ref.update}
use std::stream {StreamError, StreamErrorKind}
use http::body_io {
  Body.to_bytes, Body.to_bytes_limited, Body.write_chunked,
}
use http::types {Body, Transport}
use http::wire {Wire.chunk_frame, Wire.hex_i64}

def next_chunk (q : Ref (List (List U8))) : IO (Option (List U8)) := do {
  let xs <- Ref.get q;
  match xs {
    List.empty => IO.pure Option.none,
    List.cons chunk rest => do { Ref.set q rest; return (Option.some chunk) }
  }
}

def stream_from (chunks : List (List U8)) : IO (Unit -> IO (Option (List U8))) := do {
  let q : Ref (List (List U8)) <- Ref.new chunks;
  return (fn (_ : Unit) => next_chunk q)
}

/// A transport whose writes append to `sink`.
def recorder (sink : Ref (List U8)) : Transport :=
  Transport.secure
    (fn (_ : I64) => IO.pure (Result.err (StreamError.of StreamErrorKind.invalid_input "no read")))
    (fn (buf : ByteBuf) => do {
      let len := ByteBuf.length buf;
      let bytes <- ByteBuf.to_list buf len;
      let _ <- Ref.update sink (fn (acc : List U8) => List.append acc bytes);
      return (Result.ok len)
    })
    (fn (_ : Unit) => IO.pure Unit.unit)
    (fn (_ : Unit) => IO.pure 0i64)
    (fn (_ : I64) => IO.pure (Result.ok true))
    (fn (_ : I64) => IO.pure (Result.ok true))

#[test]
def test_hex_i64 : Bool :=
  Bool.and (String.beq (Wire.hex_i64 0i64) "0")
    (Bool.and (String.beq (Wire.hex_i64 16i64) "10")
      (String.beq (Wire.hex_i64 255i64) "ff"))

#[test]
def test_chunk_frame : Bool :=
  String.beq (String.from_list (Wire.chunk_frame (String.to_list "abc"))) "3\r\nabc\r\n"

#[test]
def test_to_bytes_drains_stream : IO Bool := do {
  let next <- stream_from [String.to_list "ab", String.to_list "cd"];
  let r <- Body.to_bytes (Body.stream next);
  match r {
    Result.err _ => return false,
    Result.ok bytes => return (String.beq (String.from_list bytes) "abcd")
  }
}

#[test]
def test_to_bytes_non_stream : IO Bool := do {
  let r <- Body.to_bytes (Body.text "hi");
  match r {
    Result.err _ => return false,
    Result.ok bytes => return (String.beq (String.from_list bytes) "hi")
  }
}

#[test]
def test_to_bytes_limited : IO Bool := do {
  let next1 <- stream_from [String.to_list "abcd"];
  let over <- Body.to_bytes_limited (Body.stream next1) 3i64;
  let next2 <- stream_from [String.to_list "abcd"];
  let under <- Body.to_bytes_limited (Body.stream next2) 4i64;
  let over_err := match over { Result.err _ => true, Result.ok _ => false };
  let under_ok := match under {
    Result.err _ => false,
    Result.ok bytes => String.beq (String.from_list bytes) "abcd"
  };
  return (Bool.and over_err under_ok)
}

#[test]
def test_write_chunked_wire_format : IO Bool := do {
  let sink : Ref (List U8) <- Ref.new List.empty;
  let next <- stream_from [String.to_list "ab", String.to_list "c"];
  let r <- Body.write_chunked (recorder sink) (Body.stream next);
  let written <- Ref.get sink;
  return (Bool.and (Result.is_ok r)
    (String.beq (String.from_list written) "2\r\nab\r\n1\r\nc\r\n0\r\n\r\n"))
}
