/// CSRF token tests: stability, constant-time verification, and form checks.

use moon::csrf {Csrf.check, Csrf.hidden_field, Csrf.token, Csrf.verify}
use moon::session {Session}

def session_with_id (id : String) : Session :=
  let s : Session := { id := id, data := List.empty, expires_at := 0i64 } in
  s

#[test]
def test_token_stable : Bool :=
  let s := session_with_id "sid-1" in
  String.beq (Csrf.token "secret" s) (Csrf.token "secret" s)

#[test]
def test_token_depends_on_session : Bool :=
  let a := session_with_id "sid-1" in
  let b := session_with_id "sid-2" in
  Bool.not (String.beq (Csrf.token "secret" a) (Csrf.token "secret" b))

#[test]
def test_verify_accepts_and_rejects : Bool :=
  let s := session_with_id "sid-1" in
  Bool.and
    (Csrf.verify "secret" s (Csrf.token "secret" s))
    (Bool.not (Csrf.verify "secret" s "wrong"))

#[test]
def test_hidden_field : Bool :=
  let s := session_with_id "sid-1" in
  match Csrf.hidden_field "secret" s {
    Pair.pair key value =>
      Bool.and (String.beq key "csrf_token") (String.beq value (Csrf.token "secret" s))
  }

#[test]
def test_check_form : Bool :=
  let s := session_with_id "sid-1" in
  let good := List.cons (Pair.pair "csrf_token" (Csrf.token "secret" s)) List.empty in
  let bad := List.cons (Pair.pair "csrf_token" "wrong") List.empty in
  Bool.and (Csrf.check "secret" s good) (Bool.not (Csrf.check "secret" s bad))
