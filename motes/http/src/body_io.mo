/// IO counterparts of `Body`: drain a stream, write a body to a `Transport`,
/// and frame one with `Transfer-Encoding: chunked`.
///
/// The pure serializers (`Wire.format_response`, `Wire.body_bytes`) still
/// refuse a stream: they have no IO context. These functions are the
/// IO-aware path the server uses.
///
/// `Body.stream`'s pull is `Unit -> IO (Option (List U8))`, the call shape
/// that survives the compiled backend (a closure stored in an action-typed
/// field cannot be executed when returned from a constructor).

use std::list {List.length}
use http::types {Body, Transport, Transport.write_bytes}
use http::wire {Wire.chunk_frame, Wire.terminal_chunk}
use lib::body {Body.to_bytes_pure}
use lib::uri {Uri.format_query}

/// One pull. A non-stream body answers its whole content once.
pub def Body.pull (b : Body) : IO (Option (List U8)) :=
  match b {
    Body.stream next => next Unit.unit,
    Body.empty => IO.pure Option.none,
    Body.bytes data => IO.pure (Option.some data),
    Body.text s => IO.pure (Option.some (String.to_list s)),
    Body.form fields => IO.pure (Option.some (String.to_list (Uri.format_query fields)))
  }

/// Drain the body to bytes. A stream is pulled to `Option.none`.
pub def Body.to_bytes (b : Body) : IO (Result String (List U8)) :=
  match b {
    Body.stream next => Body.drain next List.empty,
    _ => IO.pure (Result.ok (Body.to_bytes_pure b))
  }

/// Drain with a byte cap. Exceeding it is an error, never a truncated body.
pub def Body.to_bytes_limited (b : Body) (max : I64) : IO (Result String (List U8)) :=
  match b {
    Body.stream next => Body.drain_limited next List.empty 0i64 max,
    _ =>
      let bytes := Body.to_bytes_pure b in
      if I64.lt max (List.length bytes)
      then IO.pure (Result.err "body too large")
      else IO.pure (Result.ok bytes)
  }

#[terminating]
def Body.drain (next : Unit -> IO (Option (List U8))) (acc_rev : List (List U8)) : IO (Result String (List U8)) := do {
  let chunk <- next Unit.unit;
  match chunk {
    Option.none => IO.pure (Result.ok (Body.flatten acc_rev)),
    Option.some data => Body.drain next (List.cons data acc_rev)
  }
}

#[terminating]
def Body.drain_limited
    (next : Unit -> IO (Option (List U8)))
    (acc_rev : List (List U8))
    (total : I64)
    (max : I64)
    : IO (Result String (List U8)) := do {
  let chunk <- next Unit.unit;
  match chunk {
    Option.none => IO.pure (Result.ok (Body.flatten acc_rev)),
    Option.some data =>
      let next_total := I64.add total (List.length data) in
      if I64.lt max next_total
      then IO.pure (Result.err "body too large")
      else Body.drain_limited next (List.cons data acc_rev) next_total max
  }
}

def Body.flatten (chunks_rev : List (List U8)) : List U8 :=
  Body.concat_chunks (Body.reverse chunks_rev)

#[terminating]
def Body.reverse (xs : List (List U8)) : List (List U8) :=
  match xs {
    List.empty => List.empty,
    List.cons x rest => List.append (Body.reverse rest) (List.cons x List.empty)
  }

#[terminating]
def Body.concat_chunks (chunks : List (List U8)) : List U8 :=
  match chunks {
    List.empty => List.empty,
    List.cons chunk rest => List.append chunk (Body.concat_chunks rest)
  }

// ── writing ─────────────────────────────────────────────────────────────

/// Write the body to a transport with no framing of its own (the caller
/// writes a `Content-Length` head first).
pub def Body.write_all (t : Transport) (b : Body) : IO (Result String Unit) :=
  match b {
    Body.stream next => Body.write_pulls t next,
    _ => do {
      let w <- Transport.write_bytes t (Body.to_bytes_pure b);
      return (Body.unit_of_write w)
    }
  }

#[terminating]
def Body.write_pulls (t : Transport) (next : Unit -> IO (Option (List U8))) : IO (Result String Unit) := do {
  let chunk <- next Unit.unit;
  match chunk {
    Option.none => IO.pure (Result.ok Unit.unit),
    Option.some data => do {
      let w <- Transport.write_bytes t data;
      match w {
        Result.err e => IO.pure (Result.err e),
        Result.ok _ => Body.write_pulls t next
      }
    }
  }
}

/// Write a chunked body: each pull is one chunk, then the terminal chunk.
/// Empty chunks are skipped (a zero-size chunk would terminate early).
pub def Body.write_chunked (t : Transport) (b : Body) : IO (Result String Unit) :=
  match b {
    Body.stream next => Body.write_stream_chunked t next,
    _ =>
      let bytes := Body.to_bytes_pure b in
      if List.is_empty bytes
      then Body.write_terminal t
      else do {
        let w <- Transport.write_bytes t (Wire.chunk_frame bytes);
        match w {
          Result.err e => IO.pure (Result.err e),
          Result.ok _ => Body.write_terminal t
        }
      }
  }

#[terminating]
def Body.write_stream_chunked (t : Transport) (next : Unit -> IO (Option (List U8))) : IO (Result String Unit) := do {
  let chunk <- next Unit.unit;
  match chunk {
    Option.none => Body.write_terminal t,
    Option.some data =>
      if List.is_empty data
      then Body.write_stream_chunked t next
      else do {
        let w <- Transport.write_bytes t (Wire.chunk_frame data);
        match w {
          Result.err e => IO.pure (Result.err e),
          Result.ok _ => Body.write_stream_chunked t next
        }
      }
  }
}

def Body.write_terminal (t : Transport) : IO (Result String Unit) := do {
  let w <- Transport.write_bytes t Wire.terminal_chunk;
  return (Body.unit_of_write w)
}

def Body.unit_of_write (r : Result String U64) : Result String Unit :=
  match r {
    Result.err e => Result.err e,
    Result.ok _ => Result.ok Unit.unit
  }
