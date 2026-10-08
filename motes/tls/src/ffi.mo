// tls / ffi — the OpenSSL declarations `stream.mo` drives, and the named
// constants their integer arguments are too magic to inline.
//
// Declarative `#[extern "c"]` bindings, the libc.mo convention: symbols
// bind by NAME at link time, and WHICH LIBRARY they live in is a build
// fact about the mote (`[link] libs = ["ssl", "crypto"]` in mote.toml),
// not of any declaration here. The Rust host has no C bridge and warns
// that it is ignoring these -- every test in this mote that forces one is
// compiled-only (see tests/).
//
// Three OpenSSL details this file's shape encodes (plans/library-ideas/
// tls.md, Design 3):
//
//   * SNI is a macro, not a symbol. `SSL_set_tlsext_host_name` expands to
//     `SSL_ctrl(ssl, 55, 0, host)`, and a macro cannot bind by name, so
//     `stream.mo` calls `SSL_ctrl_host` with the named constant
//     `Ssl.ctrl_set_tlsext_hostname`.
//   * SNI and hostname verification are different jobs, and both are
//     required: the `SSL_ctrl` call tells the server WHICH certificate to
//     send, `SSL_set1_host` tells OpenSSL to CHECK the one that comes
//     back. Doing only the first yields a connection with no identity
//     check at all.
//   * The handshake does not fail on a bad certificate by default --
//     `SSL_connect` returns 1 and `SSL_get_verify_result` is the caller's
//     job. `stream.mo` sets `SSL_VERIFY_PEER` AND gates on a verify
//     result of `Ssl.x509_v_ok`; the Phase-4 fail-closed tests exist to
//     prove neither was quietly dropped.

/// The shared-object's method table. Every `SSL_CTX_new` call takes one;
/// the return is `Ptr` and its NULL-ness cannot be checked (no `Ptr`
/// comparison exists), so a missing method table surfaces at the first
/// int-returning step that takes the NULL `ssl` -- `SSL_set_fd`.
#[extern "c"]
def TLS_client_method : Ptr

#[extern "c"]
def SSL_CTX_new (method : Ptr) : Ptr

/// Returns 1 on success, 0 if the default trusted-cert paths could not
/// be loaded. Not gated by `stream.mo`: a failure here already turns the
/// handshake's verify-result gate into an error, which is the same
/// fail-closed outcome with a more honest step name.
#[extern "c"]
def SSL_CTX_set_default_verify_paths (ctx : Ptr) : I32

#[extern "c"]
def SSL_new (ctx : Ptr) : Ptr

/// The first int-returning step in the handshake, and therefore the step
/// that surfaces a NULL `ctx`/`ssl` from the Ptr-returning steps above
/// (`SSL_set_fd(NULL, fd)` is `-1`).
#[extern "c"]
def SSL_set_fd (ssl : Ptr) (fd : I32) : I32

/// The callback argument is NULL: `Ptr.null` (init/prelude.mo) exists for
/// exactly this call.
#[extern "c"]
def SSL_set_verify (ssl : Ptr) (mode : I32) (callback : Ptr) : Unit

/// The identity check -- see the module doc's third point.
#[extern "c"]
def SSL_set1_host (ssl : Ptr) (host : String) : I32

/// The generic `SSL_ctrl`: `parg` is a pointer payload. Not used by
/// `stream.mo` directly; `SSL_ctrl_host` below is the spelling whose
/// `parg` is a `String`.
#[extern "c"]
def SSL_ctrl (ssl : Ptr) (cmd : I32) (larg : I64) (parg : Ptr) : I64

/// The SNI call: `SSL_ctrl` with a `String` payload, so the emitted
/// String param wrapper hands OpenSSL a `char*` (there is no
/// String-to-Ptr conversion, and no need for one). Same link target,
/// different Monad param type.
#[extern "c" {link_name := "SSL_ctrl"}]
def SSL_ctrl_host (ssl : Ptr) (cmd : I32) (larg : I64) (parg : String) : I64

#[extern "c"]
def SSL_connect (ssl : Ptr) : I32

#[extern "c"]
def SSL_get_verify_result (ssl : Ptr) : I64

#[extern "c"]
def SSL_read (ssl : Ptr) (buf : Ptr) (num : I32) : I32

#[extern "c"]
def SSL_write (ssl : Ptr) (buf : Ptr) (num : I32) : I32

#[extern "c"]
def SSL_get_error (ssl : Ptr) (ret : I32) : I32

#[extern "c"]
def SSL_shutdown (ssl : Ptr) : I32

#[extern "c"]
def SSL_free (ssl : Ptr) : Unit

#[extern "c"]
def SSL_CTX_free (ctx : Ptr) : Unit

// ─── Named constants ─────────────────────────────────────────────────
// The numbers are the OpenSSL macros' values, spelled once. No `I32`
// literal exists in this corpus, so the `I32`-typed ones are built with
// `I64.to_i32` at the use site, which keeps these defs pure and
// interpreter-safe.

/// `SSL_CTRL_SET_TLSEXT_HOSTNAME` -- the SNI command code.
def Ssl.ctrl_set_tlsext_hostname : I32 := I64.to_i32 55

/// `SSL_VERIFY_PEER` -- require a certificate, and make the verify
/// result meaningful.
def Ssl.verify_peer : I32 := I64.to_i32 1

/// `X509_V_OK` -- what `SSL_get_verify_result` returns for a certificate
/// that actually verified.
def Ssl.x509_v_ok : I64 := 0

/// The `SSL_get_error` codes `stream.mo` distinguishes. Only the ones it
/// acts on are named; everything else falls into the final else.
def Ssl.error_none : I32 := I64.to_i32 0
def Ssl.error_ssl : I32 := I64.to_i32 1
def Ssl.error_want_read : I32 := I64.to_i32 2
def Ssl.error_want_write : I32 := I64.to_i32 3
def Ssl.error_syscall : I32 := I64.to_i32 5
def Ssl.error_zero_return : I32 := I64.to_i32 6