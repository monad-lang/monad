/// Pending authorizations: `state`, `nonce`, PKCE verifier, and the
/// redirect URI each was started for.
///
/// Single-process, in-memory store (the plan's stated limitation). Two
/// security properties live here:
///
///   * `take` is ONE-TIME. The matching entry is removed even when the
///     redirect URI does not match, so a wrong-redirect probe burns the
///     state instead of leaving it for a second try.
///   * the store is capped. At the cap it REJECTS rather than evicting a
///     live login (eviction would let an attacker push a victim's pending
///     authorization out).
///
/// Timestamps are epoch milliseconds (`IO.current_time`'s unit), so
/// `ttl_seconds` is scaled by 1000.

use std::list {List.filter, List.length}
use std::ref {Ref, Ref.new, Ref.update}
use crypto::ct {Ct.eq}
use std::random {Random.token, RandomError}
use crypto::random {CryptoRandom.new}
use lib::errors {OauthError}
use lib::pkce {Pkce.verifier}

pub struct PendingAuth {
  state : String,
  nonce : String,
  verifier : String,
  redirect_uri : String,
  created_at : I64,
  return_to : Option String
}

pub struct StateCell {
  entries : List PendingAuth,
  taken : Option PendingAuth,
  added : Bool
}

pub struct OauthStateStore {
  cell : Ref StateCell,
  ttl_seconds : I64,
  max_pending : I64
}

// ── pure store operations ────────────────────────────────────────────────

def State.empty_cell : StateCell :=
  let c : StateCell := { entries := List.empty, taken := Option.none, added := false } in
  c

def State.mk_pending
  (state : String) (nonce : String) (verifier : String) (redirect_uri : String)
  (created_at : I64) (return_to : Option String)
  : PendingAuth :=
  let p : PendingAuth := {
    state := state,
    nonce := nonce,
    verifier := verifier,
    redirect_uri := redirect_uri,
    created_at := created_at,
    return_to := return_to
  } in
  p

def State.is_live (now_ms : I64) (ttl_seconds : I64) (p : PendingAuth) : Bool :=
  match p {
    { created_at, .. } =>
      I64.gt (I64.add created_at (I64.mul ttl_seconds 1000i64)) now_ms
  }

def State.same (a : String) (b : String) : Bool :=
  Ct.eq (String.to_list a) (String.to_list b)

def State.reject (live : List PendingAuth) : StateCell :=
  let c : StateCell := { entries := live, taken := Option.none, added := false } in
  c

def State.accept (live : List PendingAuth) (p : PendingAuth) : StateCell :=
  let c : StateCell := { entries := List.cons p live, taken := Option.none, added := true } in
  c

def State.begin_pure
  (now_ms : I64) (ttl_seconds : I64) (max_pending : I64)
  (state : String) (nonce : String) (verifier : String) (redirect_uri : String)
  (return_to : Option String) (cell : StateCell)
  : StateCell :=
  match cell {
    { entries, .. } =>
      State.begin_live now_ms ttl_seconds max_pending entries
        (State.mk_pending state nonce verifier redirect_uri now_ms return_to)
  }

def State.begin_live
  (now_ms : I64) (ttl_seconds : I64) (max_pending : I64)
  (entries : List PendingAuth) (p : PendingAuth)
  : StateCell :=
  let live := List.filter (State.is_live now_ms ttl_seconds) entries in
  if I64.gt (List.length live) (I64.sub max_pending 1i64)
  then State.reject live
  else State.accept live p

/// Remove the first entry whose state matches. A matching state is
/// consumed whether or not the redirect URI matches; `taken` is `Some`
/// only when both do.
#[terminating]
def State.pull
  (want_state : String) (want_redirect : String)
  (xs : List PendingAuth) (seen : List PendingAuth)
  : Pair (List PendingAuth) (Option PendingAuth) :=
  match xs {
    List.empty => Pair.pair (List.reverse seen) Option.none,
    List.cons p rest =>
      match p {
        { state, nonce, verifier, redirect_uri, created_at, return_to } =>
          if State.same state want_state
          then
            let remaining := List.append (List.reverse seen) rest in
            if State.same redirect_uri want_redirect
            then Pair.pair remaining
                   (Option.some (State.mk_pending state nonce verifier redirect_uri created_at return_to))
            else Pair.pair remaining Option.none
          else State.pull want_state want_redirect rest
                 (List.cons (State.mk_pending state nonce verifier redirect_uri created_at return_to) seen)
      }
  }

def State.take_pure
  (now_ms : I64) (ttl_seconds : I64) (want_state : String) (want_redirect : String)
  (cell : StateCell)
  : StateCell :=
  match cell {
    { entries, .. } =>
      match State.pull want_state want_redirect
              (List.filter (State.is_live now_ms ttl_seconds) entries) List.empty {
        Pair.pair remaining found =>
          let out : StateCell := {
            entries := remaining,
            taken := found,
            added := false
          } in
          out
      }
  }

// ── the store ────────────────────────────────────────────────────────────

pub def OauthStateStore.new (ttl_seconds : I64) (max_pending : I64) : IO OauthStateStore := do {
  let ttl := if I64.lt ttl_seconds 1i64 then 1i64 else ttl_seconds;
  let cap := if I64.lt max_pending 1i64 then 1i64 else max_pending;
  let cell <- Ref.new State.empty_cell;
  let st : OauthStateStore := { cell := cell, ttl_seconds := ttl, max_pending := cap };
  return st
}

def OauthStateStore.begin_ref
  (cell : Ref StateCell) (ttl_seconds : I64) (max_pending : I64) (now_ms : I64)
  (state : String) (nonce : String) (verifier : String) (redirect_uri : String)
  (return_to : Option String)
  : IO (Result OauthError PendingAuth) := do {
  let next <- Ref.update cell
    (State.begin_pure now_ms ttl_seconds max_pending state nonce verifier redirect_uri return_to);
  return (match next {
    { added, entries, .. } =>
      if added
      then match entries {
        List.cons head _ => Result.ok head,
        List.empty => Result.err OauthError.state_too_many_pending
      }
      else Result.err OauthError.state_too_many_pending
  })
}

def OauthStateStore.begin_at
  (st : OauthStateStore) (now_ms : I64)
  (state : String) (nonce : String) (verifier : String)
  (redirect_uri : String) (return_to : Option String)
  : IO (Result OauthError PendingAuth) :=
  match st {
    { cell, ttl_seconds, max_pending } =>
      OauthStateStore.begin_ref cell ttl_seconds max_pending now_ms
        state nonce verifier redirect_uri return_to
  }

def OauthStateStore.take_ref
  (cell : Ref StateCell) (ttl_seconds : I64) (now_ms : I64)
  (state : String) (redirect_uri : String)
  : IO (Option PendingAuth) := do {
  let next <- Ref.update cell (State.take_pure now_ms ttl_seconds state redirect_uri);
  return (match next {
    { taken, .. } => taken
  })
}

def OauthStateStore.take_at
  (st : OauthStateStore) (now_ms : I64) (state : String) (redirect_uri : String)
  : IO (Option PendingAuth) :=
  match st {
    { cell, ttl_seconds, .. } =>
      OauthStateStore.take_ref cell ttl_seconds now_ms state redirect_uri
  }

def OauthStateStore.begin_results
  (st : OauthStateStore) (now_ms : I64) (redirect_uri : String) (return_to : Option String)
  (state_r : Result RandomError String) (nonce_r : Result RandomError String)
  (verifier_r : Result RandomError String)
  : IO (Result OauthError PendingAuth) := do {
  match state_r {
    Result.err _ => return (Result.err OauthError.rng_failed),
    Result.ok state =>
      match nonce_r {
        Result.err _ => return (Result.err OauthError.rng_failed),
        Result.ok nonce =>
          match verifier_r {
            Result.err _ => return (Result.err OauthError.rng_failed),
            Result.ok verifier =>
              OauthStateStore.begin_at st now_ms state nonce verifier redirect_uri return_to
          }
      }
  }
}

/// Start an authorization: three fresh 32-byte tokens (state, nonce,
/// verifier) and a pending entry bound to `redirect_uri`.
pub def OauthStateStore.begin
  (st : OauthStateStore) (redirect_uri : String) (return_to : Option String)
  : IO (Result OauthError PendingAuth) := do {
  let now <- IO.current_time;
  let state_r <- Random.token CryptoRandom.new 32i64;
  let nonce_r <- Random.token CryptoRandom.new 32i64;
  let verifier_r <- Pkce.verifier;
  OauthStateStore.begin_results st now redirect_uri return_to state_r nonce_r verifier_r
}

/// Consume `state`. `Option.none` for an unknown, expired, or
/// already-taken state, and for a redirect-URI mismatch (which also burns
/// the entry).
pub def OauthStateStore.take
  (st : OauthStateStore) (state : String) (redirect_uri : String)
  : IO (Option PendingAuth) := do {
  let now <- IO.current_time;
  OauthStateStore.take_at st now state redirect_uri
}
