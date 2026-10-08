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

use std::bytebuf {ByteBuf, ByteBuf.alloc, ByteBuf.free, ByteBuf.of_list, ByteBuf.ptr, ByteBuf.to_list}
use std::io {IO.tcp_close, IO.tcp_connect, IO.tcp_fd, Socket}
use std::list {List.length}
use lib::ffi {
  SSL_connect, SSL_CTX_free, SSL_CTX_new, SSL_CTX_set_default_verify_paths,
  SSL_ctrl_host, SSL_free, SSL_get_error, SSL_get_verify_result, SSL_new,
  SSL_read, SSL_set1_host, SSL_set_fd, SSL_set_verify, SSL_shutdown,
  SSL_write, TLS_client_method,
  Ssl.ctrl_set_tlsext_hostname, Ssl.error_none, Ssl.error_ssl,
  Ssl.error_syscall, Ssl.error_want_read, Ssl.error_want_write,
  Ssl.error_zero_return, Ssl.verify_peer, Ssl.x509_v_ok,
}

/// The live client connection: the OpenSSL handle, its context (close
/// frees both, and the ctx is unreachable without the stream), and the
/// socket they ride on (close closes it, and `SSL_set_fd` bound the ssl
/// to this descriptor specifically).
struct Tls.Stream {
  ssl : Ptr,
  ctx : Ptr,
  sock : Socket
}

/// Open a TLS connection to `host:port` with certificate verification
/// and a hostname check, or explain which step failed and how.
pub def Tls.connect (host : String) (port : U16) : IO (Result String Tls.Stream) := do {
  let method : Ptr := TLS_client_method;
  let ctx : Ptr := SSL_CTX_new method;
  // Not gated (see ffi.mo): a failure here resurfaces as the verify-result
  // error below, which is the same fail-closed outcome.
  let paths : I32 := SSL_CTX_set_default_verify_paths ctx;
  let ssl : Ptr := SSL_new ctx;
  let conn_res <- IO.tcp_connect host port;
  match conn_res {
    Result.err e => return (Result.err (String.concat "tls: tcp_connect: " e)),
    Result.ok sock => do {
      let fd <- IO.tcp_fd sock;
      let set_fd : I32 := SSL_set_fd ssl fd;
      // The first int-returning step, and therefore where a NULL ctx or
      // ssl from the Ptr-returning steps above surfaces (ffi.mo).
      if Bool.not (I32.beq set_fd (I64.to_i32 1))
      then return (Result.err "tls: SSL_set_fd failed (SSL_CTX_new or SSL_new returned NULL)")
      else do {
        let verify_set : Unit := SSL_set_verify ssl Ssl.verify_peer Ptr.null;
        let sni : I64 := SSL_ctrl_host ssl Ssl.ctrl_set_tlsext_hostname 0 host;
        if Bool.not (I64.beq sni 1)
        then Tls.abort ssl ctx sock "tls: SNI (SSL_ctrl SSL_CTRL_SET_TLSEXT_HOSTNAME) failed"
        else do {
          let set_host : I32 := SSL_set1_host ssl host;
          if Bool.not (I32.beq set_host (I64.to_i32 1))
          then Tls.abort ssl ctx sock "tls: SSL_set1_host failed"
          else do {
            let handshake : I32 := SSL_connect ssl;
            if Bool.not (I32.beq handshake (I64.to_i32 1))
            // The verify result rides along: without it every certificate
            // failure reports the same SSL_ERROR_SSL, and the caller cannot
            // tell expired (10) from hostname-mismatch (62) from self-signed.
            then Tls.abort ssl ctx sock
              (String.concat "tls: SSL_connect failed: "
                (String.concat (Tls.ssl_error_message (SSL_get_error ssl handshake))
                  (String.concat " (verify result "
                    (String.concat (I64.to_string (SSL_get_verify_result ssl)) ")"))))
            else do {
              let verify : I64 := SSL_get_verify_result ssl;
              if Bool.not (I64.beq verify Ssl.x509_v_ok)
              then Tls.abort ssl ctx sock
                (String.concat "tls: certificate verify failed: "
                  (String.concat (I64.to_string verify) " (X509_V_OK is 0)"))
              else return (Result.ok ({ ssl := ssl, ctx := ctx, sock := sock } : Tls.Stream))
            }
          }
        }
      }
    }
  }
}

/// Release everything a failed handshake set up, then report the error.
/// `SSL_shutdown` is deliberately absent: the connection never completed,
/// so there is no shutdown to attempt, only three things to release.
def Tls.abort (ssl : Ptr) (ctx : Ptr) (sock : Socket) (msg : String) : IO (Result String Tls.Stream) := do {
  let free_ssl : Unit := SSL_free ssl;
  let free_ctx : Unit := SSL_CTX_free ctx;
  let closed <- IO.tcp_close sock;
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
  let sock : Socket := s.sock;
  let shutdown : I32 := SSL_shutdown ssl;
  let free_ssl : Unit := SSL_free ssl;
  let free_ctx : Unit := SSL_CTX_free ctx;
  IO.tcp_close sock
}

// ── Reading and writing ─────────────────────────────────────────────────
//
// A fixed 4096-byte chunk on both sides: `SSL_read`/`SSL_write` take a C
// `int` count, no U64-to-I32 conversion exists, and callers (`moose`) ask
// for 4096 anyway. `max` is therefore interface parity with
// `Transport.read`, not a live bound -- callers wanting less than a chunk
// get up to a chunk.
//
// WANT_READ/WANT_WRITE get a BOUNDED retry (`#[terminating]` attempt
// counters), not an unbounded loop: a blocking socket can still yield
// them mid-renegotiation, but "retry forever" is how a client hangs
// without a timeout to blame (see the plan's no-timeout limitation). A
// zero return from `SSL_read` is end-of-stream -- `IO.tcp_read`'s
// convention, so `moose`'s read loops terminate on exactly that.

/// Read one chunk of up to 4096 bytes from the connection.
pub def Tls.read (s : Tls.Stream) (max : U64) : IO (Result String (List U8)) := do {
  let buf <- ByteBuf.alloc 4096;
  Tls.read_attempt s.ssl buf 16
}

/// One `SSL_read` attempt, or a bounded retry on WANT_READ/WANT_WRITE.
/// `attempts` is the retry budget left; it shrinks by one per retry so
/// the recursion terminates even on a pathological socket.
#[terminating]
def Tls.read_attempt (ssl : Ptr) (buf : ByteBuf) (attempts : I64) : IO (Result String (List U8)) := do {
  let n : I32 := SSL_read ssl (ByteBuf.ptr buf) (I64.to_i32 4096);
  if I32.gt n (I64.to_i32 0)
  then do {
    let bytes <- ByteBuf.to_list buf (I32.to_i64 n);
    let freed <- ByteBuf.free buf;
    return (Result.ok bytes)
  }
  else if I32.beq n (I64.to_i32 0)
  then do {
    let freed <- ByteBuf.free buf;
    return (Result.ok List.empty)
  }
  else do {
    // n < 0: WANT_READ/WANT_WRITE retry with the SAME buffer, everything
    // else is a terminal verdict.
    let code : I32 := SSL_get_error ssl n;
    let want : Bool :=
      I32.beq code Ssl.error_want_read
      || I32.beq code Ssl.error_want_write;
    if want
    then do {
      let freed <- ByteBuf.free buf;
      if I64.gt attempts 0
      then Tls.read_retry ssl (attempts - 1)
      else return (Result.err "tls read: SSL_read stuck on WANT_READ/WANT_WRITE")
    }
    else do {
      let freed <- ByteBuf.free buf;
      if I32.beq code Ssl.error_zero_return
      then return (Result.ok List.empty)
      else return (Result.err (String.concat "tls read: " (Tls.ssl_error_message code)))
    }
  }
}

/// A WANT_READ/WANT_WRITE retry: a fresh buffer (the old one was freed)
/// and a smaller budget.
#[terminating]
def Tls.read_retry (ssl : Ptr) (attempts : I64) : IO (Result String (List U8)) := do {
  let buf <- ByteBuf.alloc 4096;
  Tls.read_attempt ssl buf attempts
}

/// Write all of `data` to the connection. The ok payload is the FULL
/// length (`IO.tcp_write`'s contract). With OpenSSL's default mode
/// `SSL_write` writes all-or-fails, and a partial count cannot be
/// resumed -- there is no pointer arithmetic to hand `SSL_write` a
/// shifted buffer -- so a partial write is reported as an error rather
/// than repeated (a repeat would duplicate the bytes that DID land).
pub def Tls.write (s : Tls.Stream) (data : List U8) : IO (Result String U64) := do {
  let len : I64 := List.length data;
  let buf <- ByteBuf.of_list data;
  Tls.write_attempt s.ssl buf len 16
}

/// One `SSL_write` attempt, retrying WANT_READ/WANT_WRITE with the SAME
/// buffer (the data must not move between retries). The buffer is freed
/// on every terminal outcome and kept alive across retries only.
#[terminating]
def Tls.write_attempt (ssl : Ptr) (buf : ByteBuf) (len : I64) (attempts : I64) : IO (Result String U64) := do {
  let n : I32 := SSL_write ssl (ByteBuf.ptr buf) (I64.to_i32 len);
  if I32.beq n (I64.to_i32 len)
  then do {
    let freed <- ByteBuf.free buf;
    return (Result.ok (I64.to_u64 len))
  }
  else if I32.gt n (I64.to_i32 0)
  then do {
    let freed <- ByteBuf.free buf;
    return (Result.err "tls write: SSL_write returned a partial write it cannot resume")
  }
  else do {
    let code : I32 := SSL_get_error ssl n;
    let want : Bool :=
      I32.beq code Ssl.error_want_read
      || I32.beq code Ssl.error_want_write;
    if want
    then do {
      if I64.gt attempts 0
      then Tls.write_attempt ssl buf len (attempts - 1)
      else do {
        let freed <- ByteBuf.free buf;
        return (Result.err "tls write: SSL_write stuck on WANT_READ/WANT_WRITE")
      }
    }
    else do {
      let freed <- ByteBuf.free buf;
      return (Result.err (String.concat "tls write: " (Tls.ssl_error_message code)))
    }
  }
}