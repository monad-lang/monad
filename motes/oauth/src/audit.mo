/// Authentication audit events.
///
/// The security rules allow only five fields in an audit line: the decision,
/// the HTTP status, the subject, the issuer, and a short reason code. Tokens,
/// codes, state, cookies and secrets never appear. Subject/issuer values come
/// from the IdP, so control characters are stripped before rendering — a
/// claim cannot forge a log line.
///
/// The hook is the function type `AuditEvent -> IO Unit`; applications pass
/// it to `BearerValidator.with_audit` / `Login.with_audit`.

use http::types {Status.forbidden, Status.internal_server_error, Status.service_unavailable, Status.unauthorized}
use lib::errors {AuthError}

pub type AuditDecision {
    audit_allowed,
    audit_denied
}

pub struct AuditEvent {
    decision : AuditDecision,
    status : U16,
    subject : Option String,
    issuer : Option String,
    reason : String
}

pub def Audit.reason_of (e : AuthError) : String :=
    match e {
        AuthError.auth_missing_token => "missing_token",
        AuthError.auth_invalid_token _ => "invalid_token",
        AuthError.auth_expired => "expired",
        AuthError.auth_insufficient_scope _ => "insufficient_scope",
        AuthError.auth_temporarily_unavailable => "temporarily_unavailable",
        AuthError.auth_server_misconfigured => "server_misconfigured"
    }

pub def Audit.status_of (e : AuthError) : U16 :=
    match e {
        AuthError.auth_missing_token => Status.unauthorized,
        AuthError.auth_invalid_token _ => Status.unauthorized,
        AuthError.auth_expired => Status.unauthorized,
        AuthError.auth_insufficient_scope _ => Status.forbidden,
        AuthError.auth_temporarily_unavailable => Status.service_unavailable,
        AuthError.auth_server_misconfigured => Status.internal_server_error
    }

pub def Audit.allowed
    (status : U16) (subject : String) (issuer : String)
    : AuditEvent :=
    let e : AuditEvent := {
        decision := AuditDecision.audit_allowed,
        status := status,
        subject := Option.some subject,
        issuer := Option.some issuer,
        reason := ""
    } in
    e

pub def Audit.denied (e : AuthError) : AuditEvent :=
    let out : AuditEvent := {
        decision := AuditDecision.audit_denied,
        status := Audit.status_of e,
        subject := Option.none,
        issuer := Option.none,
        reason := Audit.reason_of e
    } in
    out

pub def Audit.denied_status (status : U16) (reason : String) : AuditEvent :=
    let out : AuditEvent := {
        decision := AuditDecision.audit_denied,
        status := status,
        subject := Option.none,
        issuer := Option.none,
        reason := reason
    } in
    out

/// The one hook dispatcher shared by the bearer and login flows.
pub def Audit.emit
    (audit : Option (AuditEvent -> IO Unit)) (e : AuditEvent)
    : IO Unit :=
    match audit {
        Option.none => return unit,
        Option.some hook => hook e
    }

/// One field byte: control and non-ASCII bytes (including U+0085/U+2028
/// separators) are dropped; quotes and backslashes are escaped.
def Audit.escape_one (b : U8) : List U8 :=
    if U8.lt b 32u8 || U8.beq b 127u8 || U8.lt 126u8 b
    then List.empty
    else if U8.beq b 34u8 then [92u8, 34u8]
    else if U8.beq b 92u8 then [92u8, 92u8]
    else [b]

#[terminating]
def Audit.escape_bytes (bs : List U8) : List U8 :=
    match bs {
        List.empty => List.empty,
        List.cons b rest =>
            List.append (Audit.escape_one b) (Audit.escape_bytes rest)
    }

/// A quoted, single-line audit field. A subject containing spaces or `=` is
/// contained by the quotes, so it cannot forge another field.
pub def Audit.quoted (s : String) : String :=
    String.concat "\""
        (String.concat (String.from_list (Audit.escape_bytes (String.to_list s))) "\"")

def Audit.decision_text (d : AuditDecision) : String :=
    match d {
        AuditDecision.audit_allowed => "allowed",
        AuditDecision.audit_denied => "denied"
    }

pub def AuditEvent.render (e : AuditEvent) : String :=
    let subject :=
        match e.subject {
            Option.none => "",
            Option.some s => " sub=" ++ Audit.quoted s
        } in
    let issuer :=
        match e.issuer {
            Option.none => "",
            Option.some s => " iss=" ++ Audit.quoted s
        } in
    let reason :=
        if String.is_empty e.reason then "" else " reason=" ++ Audit.quoted e.reason in
    "oauth " ++ Audit.decision_text e.decision
        ++ " status=" ++ U16.to_string e.status
        ++ subject ++ issuer ++ reason
