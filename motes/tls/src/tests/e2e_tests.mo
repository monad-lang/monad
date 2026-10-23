/// tls / tests / e2e — fail-closed against the real internet, env-gated.
///
/// These force `#[extern "c"]` calls, so they are compiled-backend only:
/// under the Rust interpreter, forcing `SSL_connect` fails `unknown native`.
/// They also talk to badssl.com, so every test first consults
/// `tls_network_enabled` and passes trivially when the env is unset --
/// the first env-gated tests in the corpus, because a suite that needs
/// the network cannot run in the offline sweep or a hermetic CI lane:
///
///   MONAD_TLS_NETWORK_TESTS=1 target-monad/<dir>/monad test motes/tls
///
/// The point (tls.md Phase 4): each bad certificate must fail FOR ITS OWN
/// REASON. `Tls.connect` puts the OpenSSL verify result in the error, so
/// the assertions pin the exact code -- expired is 10
/// (X509_V_ERR_CERT_HAS_EXPIRED), hostname mismatch is 62
/// (X509_V_ERR_HOSTNAME_MISMATCH, the `SSL_set1_host` regression case:
/// without that call this handshake SUCCEEDS), self-signed is 18
/// (X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT). Asserting `Result.is_err`
/// alone would pass a client that fails closed for the wrong reason.

use std::io {IO.get_env, IO.println}
use lib::stream {
  Tls.Stream, Tls.close, Tls.connect, Tls.has_pending, Tls.pending, Tls.read,
  Tls.set_timeout, Tls.write,
}
use std::bytebuf {ByteBuf, ByteBuf.free, ByteBuf.length, ByteBuf.of_string, ByteBuf.to_string}
use std::stream {StreamError}

/// True when the network gate is set. Unset means "not running these".
def tls_network_enabled : IO Bool := do {
  let env <- IO.get_env "MONAD_TLS_NETWORK_TESTS";
  match env {
    Option.none => return false,
    Option.some v => return (Bool.not (String.beq v ""))
  }
}

/// badssl.com drops connections outright at a meaningful rate (curl sees
/// it too: SSL error 35 mid-handshake), and a drop is NOT a certificate
/// verdict -- it is `SSL_ERROR_SYSCALL` with verify result 0. So a
/// dropped attempt is retried a bounded number of times, while the two
/// verdicts that MATTER stay terminal: an accepted bad certificate
/// (fail-open) and a rejection naming the wrong verify code.
def is_transient (e : String) : Bool :=
  String.contains e "SSL_ERROR_SYSCALL" || String.contains e "tcp_connect"

#[terminating]
def fails_closed_attempt (host : String) (token : String) (attempts : I64) : IO Bool := do {
  let res <- Tls.connect host 443u16;
  match res {
    Result.ok s => do { Tls.close s; IO.println (host ++ ": accepted a bad certificate"); return false },
    Result.err e =>
      if String.contains e token
      then return true
      else if Bool.and (is_transient e) (I64.gt attempts 0)
      then fails_closed_attempt host token (attempts - 1)
      else do { IO.println (host ++ ": " ++ e); return false }
  }
}

/// `Tls.connect host 443` fails AND names `token` in its message, with
/// retries for a fixture host that sometimes just drops connections. A
/// SUCCESS on a bad certificate is fail-open -- close the stream and
/// report it, never reward it. Either way the message goes to stdout:
/// a wrong verify code or an unexpected handshake is a fact about the
/// OpenSSL build, and the test output is where to read it.
def fails_closed_with (host : String) (token : String) : IO Bool :=
  fails_closed_attempt host token 5

/// The handshake retried across a fixture host that sometimes just
/// drops connections (see `is_transient`). Success is terminal; the
/// last error is what a failed run reports.
#[terminating]
def connect_retry (host : String) (attempts : I64) : IO (Result String Tls.Stream) := do {
  let res <- Tls.connect host 443u16;
  match res {
    Result.ok s => return (Result.ok s),
    Result.err e =>
      if Bool.and (is_transient e) (I64.gt attempts 0)
      then connect_retry host (attempts - 1)
      else return (Result.err e)
  }
}

/// The known-good handshake: badssl.com's own certificate is valid, so
/// this is the test that FAILS if verification is accidentally strict
/// (or the handshake is broken outright). One write then one read prove
/// bytes flow both ways through `SSL_write`/`SSL_read`, not just that
/// the handshake completed.
#[test]
def test_tls_handshake_known_good : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else do {
    let res <- connect_retry "badssl.com" 5;
    match res {
      Result.err e => do { IO.println ("badssl.com: " ++ e); return false },
      Result.ok s => known_good_exchange s
    }
  }
}

/// One GET written, one chunk read back; true when it is an HTTP/1.1 reply.
def known_good_exchange (s : Tls.Stream) : IO Bool := do {
  let get <- ByteBuf.of_string "GET / HTTP/1.1\r\nHost: badssl.com\r\nConnection: close\r\n\r\n";
  let w <- Tls.write s get;
  let _ <- ByteBuf.free get;
  let r <- Tls.read s 4096;
  Tls.close s;
  known_good_verdict w r
}

def known_good_verdict (w : Result StreamError I64) (r : Result StreamError ByteBuf) : IO Bool :=
  match w {
    Result.err e => do { IO.println ("badssl.com write: " ++ e.message); return false },
    Result.ok _ => known_good_reply r
  }

def known_good_reply (r : Result StreamError ByteBuf) : IO Bool :=
  match r {
    Result.err e => do { IO.println ("badssl.com read: " ++ e.message); return false },
    Result.ok chunk => do {
      let text <- ByteBuf.to_string chunk (ByteBuf.length chunk);
      let _ <- ByteBuf.free chunk;
      return (String.contains text "HTTP/1.1")
    }
  }

/// `SSL_has_pending` links and answers on a live connection. The truth
/// is peer-dependent (TLS 1.3 tickets), so the pinned invariant is the
/// superset relation: processed plaintext implies buffered data.
#[test]
def test_tls_has_pending_on_a_live_connection : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else do {
    let res <- connect_retry "badssl.com" 5;
    match res {
      Result.err e => do { IO.println ("has_pending: " ++ e); return false },
      Result.ok s => do {
        let processed : I64 := Tls.pending s;
        let buffered : Bool := Tls.has_pending s;
        Tls.close s;
        return (Bool.not (I64.gt processed 0) || buffered)
      }
    }
  }
}

/// `Tls.set_timeout` re-bounds a live stream; the same stream can still
/// carry a request afterwards, so the re-bound value did not corrupt it.
#[test]
def test_tls_set_timeout_rebounds_a_live_connection : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else do {
    let res <- connect_retry "badssl.com" 5;
    match res {
      Result.err e => do { IO.println ("set_timeout: " ++ e); return false },
      Result.ok s => do {
        let set_res <- Tls.set_timeout s 5000i64;
        match set_res {
          Result.err e => do { IO.println ("set_timeout: " ++ e.message); return false },
          Result.ok s2 => known_good_exchange s2
        }
      }
    }
  }
}

/// An expired certificate is rejected by the chain check.
#[test]
def test_tls_expired_certificate_fails : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else fails_closed_with "expired.badssl.com" "verify result 10"
}

/// A chained certificate for the WRONG hostname is rejected -- the
/// `SSL_set1_host` gate. Without that call the chain verifies and the
/// handshake succeeds, so this is the test that catches its absence.
#[test]
def test_tls_wrong_host_fails : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else fails_closed_with "wrong.host.badssl.com" "verify result 62"
}

/// A self-signed certificate is rejected: trusted store or no connection.
#[test]
def test_tls_self_signed_fails : IO Bool := do {
  let enabled <- tls_network_enabled;
  if Bool.not enabled
  then return true
  else fails_closed_with "self-signed.badssl.com" "verify result 18"
}