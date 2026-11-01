/// Audit rendering tests: only decision/status/subject/issuer/reason, and no
/// control characters from claim values.

use oauth::audit {
  Audit.allowed, Audit.denied, Audit.denied_status, Audit.reason_of,
  Audit.status_of, AuditEvent, AuditEvent.render,
}
use oauth::errors {AuthError}

def contains (haystack : String) (needle : String) : Bool :=
  String.contains haystack needle

#[test]
def test_audit_allowed_render : Bool :=
  let text := AuditEvent.render
    (Audit.allowed 200u16 "u1" "https://idp.example") in
  contains text "oauth allowed"
    && contains text "status=200"
    && contains text "sub=\"u1\""
    && contains text "iss=\"https://idp.example\""
    && Bool.not (contains text "reason=")

#[test]
def test_audit_denied_render : Bool :=
  let text := AuditEvent.render (Audit.denied AuthError.auth_expired) in
  contains text "oauth denied"
    && contains text "status=401"
    && contains text "reason=\"expired\""
    && Bool.not (contains text "secret-token")

#[test]
def test_audit_reason_and_status_matrix : Bool :=
  Audit.reason_of AuthError.auth_missing_token == "missing_token"
    && Audit.reason_of (AuthError.auth_invalid_token "x") == "invalid_token"
    && Audit.reason_of (AuthError.auth_insufficient_scope ["write"]) == "insufficient_scope"
    && Audit.reason_of AuthError.auth_temporarily_unavailable == "temporarily_unavailable"
    && Audit.status_of (AuthError.auth_insufficient_scope ["write"]) == 403u16
    && Audit.status_of AuthError.auth_temporarily_unavailable == 503u16
    && Audit.status_of AuthError.auth_server_misconfigured == 500u16

#[test]
def test_audit_strips_control_characters : Bool :=
  let text := AuditEvent.render
    (Audit.allowed 200u16 "u1\nforged admin=true" "idp.example") in
  Bool.not (contains text "\n")
    && contains text "forged admin=true"

#[test]
def test_audit_denied_status_builder : Bool :=
  let text := AuditEvent.render (Audit.denied_status 403u16 "insufficient_scope") in
  contains text "status=403" && contains text "reason=\"insufficient_scope\""

#[test]
def test_audit_quotes_field_injection : Bool :=
  let text := AuditEvent.render
    (Audit.allowed 200u16 "u1 iss=https://evil" "idp.example") in
  contains text "sub=\"u1 iss=https://evil\""
    && contains text "iss=\"idp.example\""

#[test]
def test_audit_strips_unicode_separators : Bool :=
  let sep := String.from_list [226u8, 128u8, 168u8] in
  let text := AuditEvent.render
    (Audit.allowed 200u16 ("u1" ++ sep ++ "admin=true") "idp.example") in
  Bool.not (contains text sep)
    && Bool.not (contains text "\n")
