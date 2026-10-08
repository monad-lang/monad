/// tls / tests — the interpreter-safe subset.
///
/// Everything here is pure Monad: the constants and the error mapping.
/// The rest of the mote is compiled-only (see stream.mo's module doc),
/// so the handshake, read/write and fail-closed behavior live in the
/// env-gated `e2e_tests.mo`, which runs only under the self-hosted
/// binary with `MONAD_TLS_NETWORK_TESTS` set.

use lib::ffi {
  Ssl.ctrl_set_tlsext_hostname, Ssl.error_none, Ssl.error_ssl,
  Ssl.error_syscall, Ssl.error_want_read, Ssl.error_want_write,
  Ssl.error_zero_return, Ssl.verify_peer, Ssl.x509_v_ok,
}
use lib::stream {Tls.ssl_error_message}

/// The SNI command code is 55 -- `SSL_CTRL_SET_TLSEXT_HOSTNAME`. A wrong
/// constant here is silently "no SNI", which many servers tolerate, so
/// this is the only place it is pinned.
#[test]
def test_ctrl_set_tlsext_hostname_is_55 : Bool :=
  I64.beq (I32.to_i64 Ssl.ctrl_set_tlsext_hostname) 55

/// `SSL_VERIFY_PEER` is 1.
#[test]
def test_verify_peer_is_1 : Bool :=
  I64.beq (I32.to_i64 Ssl.verify_peer) 1

/// `X509_V_OK` is 0 -- the value `Tls.connect`'s verify gate demands.
#[test]
def test_x509_v_ok_is_0 : Bool :=
  I64.beq Ssl.x509_v_ok 0

/// The `SSL_get_error` codes `Tls.read`/`write` distinguish. The values
/// are the ones OpenSSL's headers define; the names are what
/// `Tls.ssl_error_message` maps them to, one pin for both at once.
#[test]
def test_ssl_error_codes : Bool :=
  I64.beq (I32.to_i64 Ssl.error_none) 0
  && I64.beq (I32.to_i64 Ssl.error_ssl) 1
  && I64.beq (I32.to_i64 Ssl.error_want_read) 2
  && I64.beq (I32.to_i64 Ssl.error_want_write) 3
  && I64.beq (I32.to_i64 Ssl.error_syscall) 5
  && I64.beq (I32.to_i64 Ssl.error_zero_return) 6

/// `Tls.ssl_error_message` names each known code.
#[test]
def test_ssl_error_message_names_known_codes : Bool :=
  String.beq (Tls.ssl_error_message Ssl.error_none) "SSL_ERROR_NONE"
  && String.beq (Tls.ssl_error_message Ssl.error_ssl) "SSL_ERROR_SSL"
  && String.beq (Tls.ssl_error_message Ssl.error_want_read) "SSL_ERROR_WANT_READ"
  && String.beq (Tls.ssl_error_message Ssl.error_want_write) "SSL_ERROR_WANT_WRITE"
  && String.beq (Tls.ssl_error_message Ssl.error_syscall) "SSL_ERROR_SYSCALL"
  && String.beq (Tls.ssl_error_message Ssl.error_zero_return) "SSL_ERROR_ZERO_RETURN"

/// An unknown code still gets a name -- the retry loop's error strings
/// must never be empty.
#[test]
def test_ssl_error_message_names_unknown_codes : Bool :=
  String.beq (Tls.ssl_error_message (I64.to_i32 42)) "SSL_ERROR_42"