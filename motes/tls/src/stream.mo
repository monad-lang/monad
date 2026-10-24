/// tls / stream — the client surface `moose` consumes.
///
/// `Tls.connect` runs the OpenSSL handshake over a socket `std::io` opened:
/// every step of plans/library-ideas/tls.md's Design-3 sequence, with the
/// two gates that make the connection fail CLOSED rather than fail open:
/// `SSL_set_verify ssl Ssl.verify_peer Ptr.null` before `SSL_connect`, and
/// an explicit `SSL_get_verify_result == Ssl.x509_v_ok` check after it
/// (a handshake that succeeds over a bad certificate still returns
/// `Result.err` here -- `SSL_connect` returning 1 alone proves nothing).
///
/// Compiled backend only: forcing any `ffi.mo` extern under the Rust
/// interpreter fails `unknown native: SSL_connect`, so nothing in this
/// module is interpreter-testable beyond the pure helpers in `ffi.mo`.

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.length, ByteBuf.ptr, ByteBuf.truncate}
use std::io {IO.tcp_connect_timeout}
use std::stream {
  Stream, StreamError, StreamError.of, StreamErrorKind, FdStream, FdStream.raw_fd,
  FdStream.poll, FdStream.poll_read, FdStream.poll_write, FdStream.set_timeout,
}
use lib::ffi {
  SSL_connect, SSL_CTX_free, SSL_CTX_new, SSL_CTX_set_default_verify_paths,
  SSL_ctrl_host, SSL_free, SSL_get_error, SSL_get_verify_result, SSL_has_pending,
  SSL_new, SSL_pending, SSL_read, SSL_set1_host, SSL_set_fd, SSL_set_verify,
  SSL_shutdown,
  SSL_write, TLS_client_method,
  Ssl.ctrl_set_tlsext_hostname, Ssl.error_none, Ssl.error_ssl,
  Ssl.error_syscall, Ssl.error_want_read, Ssl.error_want_write,
  Ssl.error_zero_return, Ssl.verify_peer, Ssl.x509_v_ok,
}

/// The live client connection: the OpenSSL handle, its context (close
/// frees both, and the ctx is unreachable without the stream), and the
/// socket they ride on (close closes it, and `SSL_set_fd` bound the ssl
/// to this descriptor specifically).
pub struct Tls.Stream {
  ssl : Ptr,
  ctx : Ptr,
  sock : FdStream,
  /// The socket's per-read/write bound, kept so a `SSL_ERROR_SYSCALL`
  /// can be told apart from a genuine reset by elapsed time. Set at
  /// connect and re-bound by `Tls.set_timeout` (a streaming turn uses
  /// its idle bound here, not the connect bound).
  timeout_ms : I64
}

/// The default connect/read/write bound: generous enough for a slow
/// handshake, short enough that a blackholed host fails instead of
/// hanging. Callers that need another bound use `Tls.connect_timeout`.
pub def Tls.default_timeout_ms : I64 := 30000

/// Open a TLS connection to `host:port` with certificate verification
/// and a hostname check, or explain which step failed and how.
pub def Tls.connect (host : String) (port : U16) : IO (Result String Tls.Stream) :=
  Tls.connect_timeout host port Tls.default_timeout_ms

pub def Tls.connect_timeout (host : String) (port : U16) (timeout_ms : I64) : IO (Result String Tls.Stream) := do {
  let method : Ptr := TLS_client_method;
  let ctx <- IO.mk (SSL_CTX_new method);
  // Not gated (see ffi.mo): a failure here resurfaces as the verify-result
  // error below, which is the same fail-closed outcome.
  let _ <- IO.mk (SSL_CTX_set_default_verify_paths ctx);
  let ssl <- IO.mk (SSL_new ctx);
  let conn_res <- IO.tcp_connect_timeout host port timeout_ms;
  match conn_res {
    // No socket, but the ssl and its ctx are already allocated: release
    // them on every failed connect (a refused port or a timeout used to
    // leak both).
    Result.err e => do {
      Tls.abort_conn ssl ctx;
      return (Result.err (String.concat "tls: " e.message))
    },
    Result.ok sock => do {
      // The socket bound covers the handshake's blocking SSL_connect and
      // later SSL_read/SSL_write until a caller re-binds it with
      // `Tls.set_timeout`; `timeout_ms` is kept for the elapsed-time
      // classification of SSL_ERROR_SYSCALL.
      let sock_res <- FdStream.set_timeout sock timeout_ms timeout_ms;
      match sock_res {
        Result.err e => Tls.abort ssl ctx sock (String.concat "tls: socket timeout: " e.message),
        Result.ok _ => Tls.handshake ssl ctx sock host timeout_ms,
      }
    }
  }
}

/// The post-socket handshake steps, split out so the connection
/// wrapper's matches stay shallow.
def Tls.handshake (ssl : Ptr) (ctx : Ptr) (sock : FdStream) (host : String) (timeout_ms : I64) : IO (Result String Tls.Stream) := do {
  let fd <- FdStream.raw_fd sock;
  let set_fd <- IO.mk (SSL_set_fd ssl fd);
  // The first int-returning step, and therefore where a NULL ctx or
  // ssl from the Ptr-returning steps above surfaces (ffi.mo).
  if Bool.not (I32.beq set_fd (I64.to_i32 1))
  then Tls.abort ssl ctx sock "tls: SSL_set_fd failed (SSL_CTX_new or SSL_new returned NULL)"
  else do {
    let _ <- IO.mk (SSL_set_verify ssl Ssl.verify_peer Ptr.null);
    let sni <- IO.mk (SSL_ctrl_host ssl Ssl.ctrl_set_tlsext_hostname 0 host);
    if Bool.not (I64.beq sni 1)
    then Tls.abort ssl ctx sock "tls: SNI (SSL_ctrl SSL_CTRL_SET_TLSEXT_HOSTNAME) failed"
    else do {
      let set_host <- IO.mk (SSL_set1_host ssl host);
      if Bool.not (I32.beq set_host (I64.to_i32 1))
      then Tls.abort ssl ctx sock "tls: SSL_set1_host failed"
      else Tls.handshake_ssl ssl ctx sock timeout_ms
    }
  }
}

def Tls.handshake_ssl (ssl : Ptr) (ctx : Ptr) (sock : FdStream) (timeout_ms : I64) : IO (Result String Tls.Stream) := do {
  let started <- IO.current_time_nano;
  let handshake <- IO.mk (SSL_connect ssl);
  if Bool.not (I32.beq handshake (I64.to_i32 1))
  then do {
    let timed <- Tls.timed_out started timeout_ms;
    if timed
    then Tls.abort ssl ctx sock (Tls.timeout_message "tls: SSL_connect" timeout_ms)
    // The verify result rides along: without it every certificate
    // failure reports the same SSL_ERROR_SSL, and the caller cannot
    // tell expired (10) from hostname-mismatch (62) from self-signed.
    else Tls.abort ssl ctx sock
      (String.concat "tls: SSL_connect failed: "
        (String.concat (Tls.ssl_error_message (SSL_get_error ssl handshake))
          (String.concat " (verify result "
            (String.concat (I64.to_string (SSL_get_verify_result ssl)) ")"))))
  }
  else do {
    let verify : I64 := SSL_get_verify_result ssl;
    if Bool.not (I64.beq verify Ssl.x509_v_ok)
    then Tls.abort ssl ctx sock
      (String.concat "tls: certificate verify failed: "
        (String.concat (I64.to_string verify) " (X509_V_OK is 0)"))
    else return (Result.ok ({ ssl := ssl, ctx := ctx, sock := sock, timeout_ms := timeout_ms } : Tls.Stream))
  }
}

pub def Tls.timeout_message (what : String) (timeout_ms : I64) : String :=
  String.concat what
    (String.concat " timed out after "
      (String.concat (I64.to_string timeout_ms) " ms"))

/// Whether `timeout_ms` elapsed since `started` (nanoseconds). Used to
/// classify `SSL_ERROR_SYSCALL`: the socket bound (SO_RCVTIMEO) makes a
/// stalled read fail that way, without exposing errno.
pub def Tls.timed_out (started : I64) (timeout_ms : I64) : IO Bool := do {
  if timeout_ms < 1 then return false
  else do {
    let now <- IO.current_time_nano;
    let elapsed_ms : I64 := (now - started) / 1000000;
    return (Bool.not (elapsed_ms < timeout_ms))
  }
}

/// Release the ssl and ctx when the connect failed before a socket
/// existed (OpenSSL frees NULL handles safely).
def Tls.abort_conn (ssl : Ptr) (ctx : Ptr) : IO Unit := do {
  let _ <- IO.mk (SSL_free ssl);
  let _ <- IO.mk (SSL_CTX_free ctx);
  return unit
}

/// Release everything a failed handshake set up, then report the error.
/// `SSL_shutdown` is deliberately absent: the connection never completed,
/// so there is no shutdown to attempt, only three things to release.
def Tls.abort (ssl : Ptr) (ctx : Ptr) (sock : FdStream) (msg : String) : IO (Result String Tls.Stream) := do {
  let _ <- IO.mk (SSL_free ssl);
  let _ <- IO.mk (SSL_CTX_free ctx);
  let closed <- Stream.close sock;
  return (Result.err msg)
}

/// A human-readable name for an `SSL_get_error` code. An if-else chain,
/// not `match`: numeric-literal match patterns do not exist in this
/// corpus, and the constants are defs, not literals.
pub def Tls.ssl_error_message (code : I32) : String :=
  if I32.beq code Ssl.error_none then "SSL_ERROR_NONE"
  else if I32.beq code Ssl.error_ssl then "SSL_ERROR_SSL"
  else if I32.beq code Ssl.error_want_read then "SSL_ERROR_WANT_READ"
  else if I32.beq code Ssl.error_want_write then "SSL_ERROR_WANT_WRITE"
  else if I32.beq code Ssl.error_syscall then "SSL_ERROR_SYSCALL"
  else if I32.beq code Ssl.error_zero_return then "SSL_ERROR_ZERO_RETURN"
  else String.concat "SSL_ERROR_" (I32.to_string code)

/// Close a connection. `SSL_shutdown`'s return is ignored -- a failed
/// close is a diagnostic, not a reason to leak the ssl and the socket
/// that follow it. Order: shutdown bidirectionally, free the ssl, free
/// the ctx, close the socket, mirroring the handshake's construction
/// order in reverse.
pub def Tls.close (s : Tls.Stream) : IO Unit := do {
  let ssl : Ptr := s.ssl;
  let ctx : Ptr := s.ctx;
  let sock : FdStream := s.sock;
  let _ <- IO.mk (SSL_shutdown ssl);
  let _ <- IO.mk (SSL_free ssl);
  let _ <- IO.mk (SSL_CTX_free ctx);
  Stream.close sock
}

/// Re-bound a live connection's socket to `bound_ms` in both directions
/// and return the stream carrying that bound, so a later
/// `SSL_ERROR_SYSCALL` stall is classified against the same value.
///
/// Called after the handshake and BEFORE the transport closures capture
/// the stream (a streaming turn wants its idle bound here, not the
/// connect bound). On failure the connection is CLOSED before the error
/// returns: the socket cannot take the requested bound, so the stream is
/// not usable.
pub def Tls.set_timeout (s : Tls.Stream) (bound_ms : I64) : IO (Result StreamError Tls.Stream) := do {
  let sock : FdStream := s.sock;
  let set_res <- FdStream.set_timeout sock bound_ms bound_ms;
  match set_res {
    Result.err e => do {
      let _ <- Tls.close s;
      return (Result.err e)
    },
    Result.ok _ => return (Result.ok (Tls.rebound s bound_ms)),
  }
}

/// The re-bound stream value; a helper keeps the struct update out of
/// constructor-argument position (the compiled backend miscompiles a
/// bare literal there).
def Tls.rebound (s : Tls.Stream) (bound_ms : I64) : Tls.Stream :=
  ({ s with timeout_ms := bound_ms } : Tls.Stream)

// ── Reading and writing ─────────────────────────────────────────────────
//
// `Stream`'s contract (std/stream.mo), so `Transport.secure` can carry
// these where `Transport.plain` carries `Stream.read`/`write`: a read
// hands back a `ByteBuf` the caller frees, a zero-length one at end of
// stream; a write writes the whole buffer, which stays the caller's.
// Errors are `StreamErrorKind.other` carrying OpenSSL's text.
//
// A fixed 4096-byte chunk on the read side: `SSL_read` takes a C `int`
// count and callers (`moose`) ask for 4096 anyway. `max` is therefore
// interface parity with `Stream.read`, not a live bound -- callers
// wanting less than a chunk get up to a chunk.
//
// WANT_READ/WANT_WRITE get a BOUNDED retry (`#[terminating]` attempt
// counters), not an unbounded loop: a blocking socket can still yield
// them mid-renegotiation. The socket's SO_RCVTIMEO/SO_SNDTIMEO (set at
// connect, re-bound by `Tls.set_timeout`) is the hard bound; a stalled
// read surfaces as SSL_ERROR_SYSCALL and is reported `timed_out` once
// the elapsed time reaches that bound.

def Tls.error (msg : String) : StreamError := StreamError.of StreamErrorKind.other msg

/// Decrypted bytes already buffered by OpenSSL: a readiness wait must
/// not sleep while this is positive.
pub def Tls.pending (s : Tls.Stream) : I64 := I32.to_i64 (SSL_pending s.ssl)

/// Whether the SSL object can make progress without touching the
/// socket: buffered data exists, whether or not it has been decrypted
/// yet. `Tls.pending` alone misses a record sitting undecrypted in the
/// read BIO, which is exactly the case a socket poll would sleep on.
pub def Tls.has_pending (s : Tls.Stream) : Bool :=
  Bool.not (I32.beq (SSL_has_pending s.ssl) (I64.to_i32 0))

/// Wait until the connection can make progress in `timeout_ms`:
/// `ok true` ready, `ok false` timed out. Buffered TLS data counts as
/// ready without touching the socket.
pub def Tls.wait_read (s : Tls.Stream) (timeout_ms : I64) : IO (Result StreamError Bool) :=
  if Tls.has_pending s
  then IO.pure (Result.ok true)
  else FdStream.poll s.sock FdStream.poll_read timeout_ms

pub def Tls.wait_write (s : Tls.Stream) (timeout_ms : I64) : IO (Result StreamError Bool) :=
  FdStream.poll s.sock FdStream.poll_write timeout_ms

/// Read one chunk of up to 4096 bytes from the connection.
pub def Tls.read (s : Tls.Stream) (max : I64) : IO (Result StreamError ByteBuf) := do {
  let buf <- ByteBuf.alloc 4096;
  let started <- IO.current_time_nano;
  Tls.read_attempt s buf 16 started
}

/// One `SSL_read` attempt, or a bounded retry on WANT_READ/WANT_WRITE.
/// `attempts` is the retry budget left; it shrinks by one per retry so
/// the recursion terminates even on a pathological socket. A success
/// truncates the buffer to what `SSL_read` wrote and hands it over.
#[terminating]
def Tls.read_attempt (s : Tls.Stream) (buf : ByteBuf) (attempts : I64) (started : I64) : IO (Result StreamError ByteBuf) := do {
  let n <- IO.mk (SSL_read s.ssl (ByteBuf.ptr buf) (I64.to_i32 4096));
  if I32.gt n (I64.to_i32 0)
  then do {
    let _ <- ByteBuf.truncate buf (I32.to_i64 n);
    return (Result.ok buf)
  }
  else if I32.beq n (I64.to_i32 0)
  then Tls.read_eof buf
  else do {
    // n < 0: WANT_READ/WANT_WRITE retry with the SAME buffer, everything
    // else is a terminal verdict.
    let code : I32 := SSL_get_error s.ssl n;
    let want : Bool :=
      I32.beq code Ssl.error_want_read
      || I32.beq code Ssl.error_want_write;
    // A stalled socket read surfaces as SYSCALL (SO_RCVTIMEO's EAGAIN)
    // or as a WANT that never clears; only those become `timed_out`.
    let timed <- Tls.timed_out started s.timeout_ms;
    let stalled : Bool := Bool.or want (I32.beq code Ssl.error_syscall);
    if Bool.and timed stalled
    then Tls.read_timed_out buf
    else if want && I64.gt attempts 0
    then Tls.read_attempt s buf (attempts - 1) started
    else if want
    then Tls.read_failed buf "tls read: SSL_read stuck on WANT_READ/WANT_WRITE"
    else if I32.beq code Ssl.error_zero_return
    then Tls.read_eof buf
    else Tls.read_failed buf (String.concat "tls read: " (Tls.ssl_error_message code))
  }
}

/// End of stream: the same buffer, emptied (`Stream.read`'s convention).
def Tls.read_eof (buf : ByteBuf) : IO (Result StreamError ByteBuf) := do {
  let _ <- ByteBuf.truncate buf 0;
  return (Result.ok buf)
}

/// A terminal read failure: nobody else will see the buffer, so free it.
def Tls.read_failed (buf : ByteBuf) (msg : String) : IO (Result StreamError ByteBuf) := do {
  let _ <- ByteBuf.free buf;
  return (Result.err (Tls.error msg))
}

def Tls.read_timed_out (buf : ByteBuf) : IO (Result StreamError ByteBuf) := do {
  let _ <- ByteBuf.free buf;
  return (Result.err (StreamError.of StreamErrorKind.timed_out "tls read: timed out"))
}

/// Write all of `buf` to the connection. The ok payload is the FULL
/// length (`Stream.write`'s contract). With OpenSSL's default mode
/// `SSL_write` writes all-or-fails, and a partial count cannot be
/// resumed -- there is no pointer arithmetic to hand `SSL_write` a
/// shifted buffer -- so a partial write is reported as an error rather
/// than repeated (a repeat would duplicate the bytes that DID land).
pub def Tls.write (s : Tls.Stream) (buf : ByteBuf) : IO (Result StreamError I64) := do {
  let started <- IO.current_time_nano;
  Tls.write_attempt s buf (ByteBuf.length buf) 16 started
}

/// One `SSL_write` attempt, retrying WANT_READ/WANT_WRITE with the SAME
/// buffer (the data must not move between retries).
#[terminating]
def Tls.write_attempt (s : Tls.Stream) (buf : ByteBuf) (len : I64) (attempts : I64) (started : I64) : IO (Result StreamError I64) := do {
  let n <- IO.mk (SSL_write s.ssl (ByteBuf.ptr buf) (I64.to_i32 len));
  Tls.write_once s buf len attempts started n
}

#[terminating]
def Tls.write_once (s : Tls.Stream) (buf : ByteBuf) (len : I64) (attempts : I64) (started : I64) (n : I32) : IO (Result StreamError I64) :=
  if I32.beq n (I64.to_i32 len)
  then IO.pure (Result.ok len)
  else if I32.gt n (I64.to_i32 0)
  then IO.pure (Result.err (Tls.error "tls write: SSL_write returned a partial write it cannot resume"))
  else Tls.write_failed s buf len attempts started (SSL_get_error s.ssl n)

#[terminating]
def Tls.write_failed (s : Tls.Stream) (buf : ByteBuf) (len : I64) (attempts : I64) (started : I64) (code : I32) : IO (Result StreamError I64) := do {
  let want : Bool :=
    I32.beq code Ssl.error_want_read
    || I32.beq code Ssl.error_want_write;
  let timed <- Tls.timed_out started s.timeout_ms;
  let stalled : Bool := Bool.or want (I32.beq code Ssl.error_syscall);
  if Bool.and timed stalled
  then IO.pure (Result.err (StreamError.of StreamErrorKind.timed_out "tls write: timed out"))
  else if want && I64.gt attempts 0
  then Tls.write_attempt s buf len (attempts - 1) started
  else if want
  then IO.pure (Result.err (Tls.error "tls write: SSL_write stuck on WANT_READ/WANT_WRITE"))
  else IO.pure (Result.err (Tls.error (String.concat "tls write: " (Tls.ssl_error_message code))))
}
