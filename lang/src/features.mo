/// Optional-dependency and feature resolution.
///
/// Pure: the caller supplies one `FeaturePackage` per **reachable** mote
/// (its `[features]` table and its dependency policies), plus the root's
/// selection. No filesystem read happens here, which is what makes the
/// resolver unit-testable and identical in both compilers.
///
/// Rules (Cargo's model):
///   * features are additive and unioned; a dependency is enabled if any
///     dependent enables it;
///   * a non-optional dependency is always enabled with the parent's
///     `default-features` choice;
///   * an optional dependency is enabled only by `dep:name`, `name/f` or a
///     plain item naming an optional dep;
///   * `name?/f` is weak: it enables `f` only if `name` is already enabled;
///   * `default` is a feature like any other; the root's is on unless
///     `no_default`, a dependency's follows its policy.
///
/// This module is the feature half of `implementations/
/// attributes-deprecated-and-cfg.md`'s `CfgSet`; it does not do the `#[cfg]`
/// filtering itself.

pub struct DepPolicy {
  optional : Bool,
  features : List String,
  default_features : Bool
}

pub def DepPolicy.default : DepPolicy :=
  let p : DepPolicy :=
    { optional := false, features := List.empty, default_features := true } in
  p

/// One package's feature declarations and dependency policies.
pub struct FeaturePackage {
  name : String,
  features : List (Pair String (List String)),
  deps : List (Pair String DepPolicy)
}

/// The resolved answer: each package's enabled feature set, and each
/// package's enabled dependency names (non-optional plus activated
/// optional ones).
pub struct FeatureSelection {
  features : List (Pair String (List String)),
  enabled_deps : List (Pair String (List String))
}

struct FeatureState {
  selection : FeatureSelection,
  reached : List String,
  pending : List (Pair String String),
  /// Weak `name?/feature` items whose dependency was not enabled when they
  /// were first seen. Re-evaluated after the main fixed point, so resolution
  /// does not depend on feature declaration/request order.
  deferred : List (Pair String String)
}

// ── small list helpers ──────────────────────────────────────────────────

#[terminating]
def Features.mem (x : String) (xs : List String) : Bool :=
  match xs {
    List.empty => false,
    List.cons y rest => if String.beq x y then true else Features.mem x rest
  }

#[terminating]
def Features.add_unique (x : String) (xs : List String) : List String :=
  if Features.mem x xs then xs else List.cons x xs

#[terminating]
def Features.lookup (name : String)
    (assoc : List (Pair String (List String))) : List String :=
  match assoc {
    List.empty => List.empty,
    List.cons p rest =>
      match p {
        Pair.pair k v => if String.beq k name then v else Features.lookup name rest
      }
  }

#[terminating]
def Features.remove (name : String)
    (assoc : List (Pair String (List String))) : List (Pair String (List String)) :=
  match assoc {
    List.empty => List.empty,
    List.cons p rest =>
      match p {
        Pair.pair k v =>
          if String.beq k name
          then Features.remove name rest
          else List.cons (Pair.pair k v) (Features.remove name rest)
      }
  }

def Features.set (name : String) (vals : List String)
    (assoc : List (Pair String (List String))) : List (Pair String (List String)) :=
  List.cons (Pair.pair name vals) (Features.remove name assoc)

#[terminating]
def Features.find_package (name : String) (pkgs : List FeaturePackage) :
    Option FeaturePackage :=
  match pkgs {
    List.empty => Option.none,
    List.cons p rest =>
      if String.beq p.name name then Option.some p else Features.find_package name rest
  }

#[terminating]
def Features.find_feature (name : String)
    (features : List (Pair String (List String))) : Option (List String) :=
  match features {
    List.empty => Option.none,
    List.cons p rest =>
      match p {
        Pair.pair k v => if String.beq k name then Option.some v else Features.find_feature name rest
      }
  }

#[terminating]
def Features.find_policy (name : String) (deps : List (Pair String DepPolicy)) :
    Option DepPolicy :=
  match deps {
    List.empty => Option.none,
    List.cons p rest =>
      match p {
        Pair.pair k v => if String.beq k name then Option.some v else Features.find_policy name rest
      }
  }

// ── item spelling ───────────────────────────────────────────────────────
//
// One item is a plain feature/dep name, `dep:name`, `dep/feature` or
// `dep?/feature`. Parsing stays local (no dependency on http's string
// helpers, which live in another mote).

#[terminating]
def Features.find_slash (bytes : List U8) (seen : I64) : Option I64 :=
  match bytes {
    List.empty => Option.none,
    List.cons b rest =>
      if U8.beq b 47u8 then Option.some seen else Features.find_slash rest (I64.add seen 1i64)
  }

def Features.split_slash (s : String) : Option (Pair String String) :=
  match Features.find_slash (String.to_list s) 0i64 {
    Option.none => Option.none,
    Option.some i =>
      let name := String.slice s 0 i in
      let feature := String.drop (I64.add i 1i64) s in
      Option.some (Pair.pair name feature)
  }

def Features.strip_dep_prefix (s : String) : Option String :=
  if String.starts_with "dep:" s
  then Option.some (String.drop 4i64 s)
  else Option.none

/// `name?` -> `(name, true)`; `name` -> `(name, false)`.
def Features.strip_weak (s : String) : Pair String Bool :=
  if String.ends_with s "?"
  then Pair.pair (String.slice s 0 (I64.sub (String.length s) 1i64)) true
  else Pair.pair s false

// ── resolution ──────────────────────────────────────────────────────────

def Features.empty_state : FeatureState :=
  let sel : FeatureSelection :=
    { features := List.empty, enabled_deps := List.empty } in
  let st : FeatureState :=
    { selection := sel, reached := List.empty, pending := List.empty,
      deferred := List.empty } in
  st

#[terminating]
def Features.pending_has (pkg : String) (feature : String)
    (pending : List (Pair String String)) : Bool :=
  match pending {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair k f =>
          if Bool.and (String.beq k pkg) (String.beq f feature)
          then true
          else Features.pending_has pkg feature rest
      }
  }

/// Enqueue `feature` on `pkg`, optionally tolerating a missing feature
/// (`default` and a policy's `features` list may name one the dependency
/// does not declare; a CLI `--features` request may not).
def Features.enqueue (pkg : String) (feature : String) (tolerate : Bool)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  match Features.find_package pkg pkgs {
    Option.none =>
      if tolerate
      then Result.ok st
      else Result.err (String.concat "no manifest for dependency `" (String.concat pkg "`")),
    Option.some p =>
      match Features.find_feature feature p.features {
        Option.none =>
          if tolerate
          then Result.ok st
          else Result.err (String.concat "mote `"
            (String.concat pkg
              (String.concat "` has no feature `" (String.concat feature "`")))),
        Option.some _ =>
          if Bool.or (Features.mem feature (Features.lookup pkg st.selection.features))
              (Features.pending_has pkg feature st.pending)
          then Result.ok st
          else
            let st2 : FeatureState :=
              { selection := st.selection,
                reached := st.reached,
                pending := List.cons (Pair.pair pkg feature) st.pending,
                deferred := st.deferred } in
            Result.ok st2
      }
  }

#[terminating]
def Features.enqueue_all (pkg : String) (features : List String) (tolerate : Bool)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  match features {
    List.empty => Result.ok st,
    List.cons f rest =>
      match Features.enqueue pkg f tolerate pkgs st {
        Result.err e => Result.err e,
        Result.ok st2 => Features.enqueue_all pkg rest tolerate pkgs st2
      }
  }

/// Enable `dep` on `owner` and activate its package (its non-optional
/// dependencies, `default-features` choice and requested features).
#[terminating]
def Features.enable_dep (owner : String) (dep : String) (policy : DepPolicy)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  let owner_deps := Features.lookup owner st.selection.enabled_deps in
  let st1 : FeatureState :=
    { selection :=
        { st.selection with
          enabled_deps := Features.set owner (Features.add_unique dep owner_deps)
            st.selection.enabled_deps },
      reached := st.reached,
      pending := st.pending,
      deferred := st.deferred } in
  match Features.activate dep policy.default_features pkgs st1 {
    Result.err e => Result.err e,
    Result.ok st2 => Features.enqueue_all dep policy.features false pkgs st2
  }

/// Activate `pkg` once: mark it reached, enqueue `default` if asked, then
/// activate every non-optional dependency it declares.
#[terminating]
def Features.activate (pkg : String) (with_default : Bool)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  if Features.mem pkg st.reached
  then Result.ok st
  else
    match Features.find_package pkg pkgs {
      Option.none => Result.err (String.concat "no manifest for dependency `" (String.concat pkg "`")),
      Option.some p =>
        let st1 : FeatureState :=
          { selection := st.selection,
            reached := List.cons pkg st.reached,
            pending := st.pending,
            deferred := st.deferred } in
        match (if with_default then Features.enqueue pkg "default" true pkgs st1
               else Result.ok st1) {
          Result.err e => Result.err e,
          Result.ok st2 => Features.activate_non_optional pkg p.deps pkgs st2
        }
    }

#[terminating]
def Features.activate_non_optional (owner : String)
    (deps : List (Pair String DepPolicy)) (pkgs : List FeaturePackage)
    (st : FeatureState) : Result String FeatureState :=
  match deps {
    List.empty => Result.ok st,
    List.cons p rest =>
      match p {
        Pair.pair name policy =>
          if policy.optional
          then Features.activate_non_optional owner rest pkgs st
          else match Features.enable_dep owner name policy pkgs st {
            Result.err e => Result.err e,
            Result.ok st2 => Features.activate_non_optional owner rest pkgs st2
          }
      }
  }

/// Process one feature item on behalf of `owner`.
def Features.process_item (owner : String) (item : String)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  match Features.strip_dep_prefix item {
    Option.some dep =>
      match Features.find_package owner pkgs {
        Option.none => Result.err (String.concat "no manifest for mote `" (String.concat owner "`")),
        Option.some p =>
          match Features.find_policy dep p.deps {
            Option.none => Result.err (String.concat "feature "
              (String.concat "`" (String.concat item "` names an undeclared dependency"))),
            Option.some policy =>
              if Bool.not policy.optional
              then Result.err (String.concat "`" (String.concat item
                "` names a dependency that is not optional"))
              else Features.enable_dep owner dep policy pkgs st
          }
      },
    Option.none =>
      match Features.split_slash item {
        Option.none => Features.process_plain owner item pkgs st,
        Option.some pr =>
          match pr {
            Pair.pair raw_dep feature =>
              match Features.strip_weak raw_dep {
                Pair.pair dep weak =>
                  match Features.find_package owner pkgs {
                    Option.none =>
                      Result.err (String.concat "no manifest for mote `" (String.concat owner "`")),
                    Option.some p =>
                      match Features.find_policy dep p.deps {
                        Option.none => Result.err (String.concat "feature `"
                          (String.concat item "` names an undeclared dependency")),
                        Option.some policy =>
                          if weak
                          then
                            if Features.mem dep (Features.lookup owner st.selection.enabled_deps)
                            then Features.enqueue dep feature false pkgs st
                            else Features.defer owner item st
                          else match Features.enable_dep owner dep policy pkgs st {
                            Result.err e => Result.err e,
                            Result.ok st2 => Features.enqueue dep feature false pkgs st2
                          }
                      }
                  }
              }
          }
      }
  }

#[terminating]
def Features.deferred_has (owner : String) (item : String)
    (items : List (Pair String String)) : Bool :=
  match items {
    List.empty => false,
    List.cons p rest =>
      match p {
        Pair.pair o i =>
          if Bool.and (String.beq o owner) (String.beq i item)
          then true
          else Features.deferred_has owner item rest
      }
  }

def Features.defer (owner : String) (item : String) (st : FeatureState) :
    Result String FeatureState :=
  if Features.deferred_has owner item st.deferred
  then Result.ok st
  else
    let st2 : FeatureState :=
      { selection := st.selection, reached := st.reached, pending := st.pending,
        deferred := List.cons (Pair.pair owner item) st.deferred } in
    Result.ok st2

/// Re-evaluate deferred weak items once the main fixed point is stable.
/// Returns the state and whether anything new was queued.
#[terminating]
def Features.apply_deferred (pkgs : List FeaturePackage)
    (items : List (Pair String String)) (st : FeatureState) (changed : Bool) :
    Result String (Pair FeatureState Bool) :=
  match items {
    List.empty => Result.ok (Pair.pair st changed),
    List.cons p rest =>
      match p {
        Pair.pair owner item =>
          match Features.split_slash item {
            Option.none =>
              Features.apply_deferred pkgs rest st changed,
            Option.some pr =>
              match pr {
                Pair.pair raw_dep feature =>
                  match Features.strip_weak raw_dep {
                    Pair.pair dep weak =>
                      if Bool.not weak
                      then Features.apply_deferred pkgs rest st changed
                      else if Features.mem dep (Features.lookup owner st.selection.enabled_deps)
                      then
                        let already := Features.mem feature (Features.lookup dep st.selection.features) in
                        match Features.enqueue dep feature false pkgs st {
                          Result.err e => Result.err e,
                          Result.ok st2 =>
                            Features.apply_deferred pkgs rest st2
                              (Bool.or changed (Bool.not already))
                        }
                      else
                        // Keep the still-inactive item for a later pass.
                        let st2 : FeatureState :=
                          { selection := st.selection, reached := st.reached,
                            pending := st.pending,
                            deferred := List.cons (Pair.pair owner item) st.deferred } in
                        Features.apply_deferred pkgs rest st2 changed
                  }
              }
          }
      }
  }

/// A plain item is a local feature if one exists, else an implicit
/// optional-dependency enable (Cargo's older spelling).
#[terminating]
def Features.process_plain (owner : String) (item : String)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  match Features.find_package owner pkgs {
    Option.none => Result.err (String.concat "no manifest for mote `" (String.concat owner "`")),
    Option.some p =>
      match Features.find_feature item p.features {
        Option.some _ => Features.enqueue owner item false pkgs st,
        Option.none =>
          match Features.find_policy item p.deps {
            Option.some policy =>
              if policy.optional
              then Features.enable_dep owner item policy pkgs st
              else Result.err (String.concat "feature `"
                (String.concat item "` is a dependency, not a feature")),
            Option.none => Result.err (String.concat "mote `"
              (String.concat owner
                (String.concat "` has no feature `" (String.concat item "`"))))
          }
      }
  }

#[terminating]
def Features.process_items (owner : String) (items : List String)
    (pkgs : List FeaturePackage) (st : FeatureState) : Result String FeatureState :=
  match items {
    List.empty => Result.ok st,
    List.cons item rest =>
      match Features.process_item owner item pkgs st {
        Result.err e => Result.err e,
        Result.ok st2 => Features.process_items owner rest pkgs st2
      }
  }

#[terminating]
def Features.solve (pkgs : List FeaturePackage) (st : FeatureState) :
    Result String FeatureState :=
  match st.pending {
    List.empty =>
      match Features.apply_deferred pkgs (List.reverse st.deferred) st false {
        Result.err e => Result.err e,
        Result.ok pr =>
          match pr {
            Pair.pair st2 changed =>
              if changed
              then Features.solve pkgs
                { selection := st2.selection, reached := st2.reached,
                  pending := st2.pending, deferred := st2.deferred }
              else Result.ok st2
          }
      },
    List.cons p rest =>
      match p {
        Pair.pair pkg feature =>
          let st0 : FeatureState :=
            { selection := st.selection, reached := st.reached, pending := rest,
                deferred := st.deferred } in
          if Features.mem feature (Features.lookup pkg st0.selection.features)
          then Features.solve pkgs st0
          else
            match Features.find_package pkg pkgs {
              Option.none => Result.err (String.concat "no manifest for dependency `"
                (String.concat pkg "`")),
              Option.some p =>
                match Features.find_feature feature p.features {
                  Option.none => Result.err (String.concat "mote `"
                    (String.concat pkg
                      (String.concat "` has no feature `" (String.concat feature "`")))),
                  Option.some items =>
                    let st1 : FeatureState :=
                      { selection :=
                          { st0.selection with
                            features := Features.set pkg
                              (List.cons feature (Features.lookup pkg st0.selection.features))
                              st0.selection.features },
                        reached := st0.reached,
                        pending := st0.pending,
                        deferred := st0.deferred } in
                    match Features.process_items pkg items pkgs st1 {
                      Result.err e => Result.err e,
                      Result.ok st2 => Features.solve pkgs st2
                    }
                }
            }
      }
  }

/// Resolve a root's features. `requested` are the CLI/target features;
/// `no_default` drops only the root's `default`.
pub def Features.resolve (pkgs : List FeaturePackage) (root : String)
    (requested : List String) (no_default : Bool) : Result String FeatureSelection :=
  match Features.find_package root pkgs {
    Option.none => Result.err (String.concat "no manifest for root mote `" (String.concat root "`")),
    Option.some _ =>
      match Features.activate root (Bool.not no_default) pkgs Features.empty_state {
        Result.err e => Result.err e,
        Result.ok st1 =>
          match Features.enqueue_all root requested false pkgs st1 {
            Result.err e => Result.err e,
            Result.ok st2 =>
              match Features.solve pkgs st2 {
                Result.err e => Result.err e,
                Result.ok st3 => Result.ok st3.selection
              }
          }
      }
  }

// ─── Tests ─────────────────────────────────────────────────────────────

def fdep (optional : Bool) (features : List String) (default_features : Bool) : DepPolicy :=
  let p : DepPolicy :=
    { optional := optional, features := features, default_features := default_features } in
  p

def fpkg (name : String) (features : List (Pair String (List String)))
    (deps : List (Pair String DepPolicy)) : FeaturePackage :=
  let p : FeaturePackage := { name := name, features := features, deps := deps } in
  p

def fpair (name : String) (items : List String) : Pair String (List String) :=
  Pair.pair name items

def resolved (pkgs : List FeaturePackage) (root : String)
    (requested : List String) (no_default : Bool) : Option FeatureSelection :=
  match Features.resolve pkgs root requested no_default {
    Result.ok s => Option.some s,
    Result.err _ => Option.none
  }

def selection_has_feature (sel : FeatureSelection) (pkg : String) (f : String) : Bool :=
  Features.mem f (Features.lookup pkg sel.features)

def selection_has_dep (sel : FeatureSelection) (pkg : String) (d : String) : Bool :=
  Features.mem d (Features.lookup pkg sel.enabled_deps)

def optional_fixture : List FeaturePackage := [
  fpkg "moon"
    [fpair "default" ["crypto-sessions"], fpair "crypto-sessions" ["dep:crypto"]]
    [Pair.pair "crypto" (fdep true List.empty true)],
  fpkg "crypto" [fpair "default" List.empty] List.empty
]

#[test]
def test_features_default_enables_optional_dep : Bool :=
  match resolved optional_fixture "moon" List.empty false {
    Option.none => false,
    Option.some sel =>
      Bool.and (selection_has_dep sel "moon" "crypto")
        (Bool.and (selection_has_feature sel "moon" "default")
          (selection_has_feature sel "moon" "crypto-sessions"))
  }

#[test]
def test_features_no_default_keeps_optional_off : Bool :=
  match resolved optional_fixture "moon" List.empty true {
    Option.none => false,
    Option.some sel =>
      Bool.and (Bool.not (selection_has_dep sel "moon" "crypto"))
        (Bool.not (selection_has_feature sel "moon" "default"))
  }

#[test]
def test_features_requested_reenables_without_default : Bool :=
  match resolved optional_fixture "moon" ["crypto-sessions"] true {
    Option.none => false,
    Option.some sel => selection_has_dep sel "moon" "crypto"
  }

def union_fixture : List FeaturePackage := [
  fpkg "root" [fpair "default" List.empty] [
    Pair.pair "a" (fdep false List.empty true),
    Pair.pair "c" (fdep false List.empty true)],
  fpkg "a" List.empty [Pair.pair "b" (fdep false ["f1"] true)],
  fpkg "c" List.empty [Pair.pair "b" (fdep false ["f1", "f2"] true)],
  fpkg "b" [fpair "default" List.empty, fpair "f1" List.empty, fpair "f2" List.empty] List.empty
]

#[test]
def test_features_union_across_dependents : Bool :=
  match resolved union_fixture "root" List.empty false {
    Option.none => false,
    Option.some sel =>
      Bool.and (selection_has_feature sel "b" "f1")
        (selection_has_feature sel "b" "f2")
  }

def weak_fixture : List FeaturePackage := [
  fpkg "root"
    [fpair "default" List.empty, fpair "weak" ["b?/f"], fpair "strong" ["b/f"]]
    [Pair.pair "b" (fdep true List.empty true)],
  fpkg "b" [fpair "default" List.empty, fpair "f" List.empty] List.empty
]

#[test]
def test_features_weak_does_not_enable_dep : Bool :=
  match resolved weak_fixture "root" ["weak"] true {
    Option.none => false,
    Option.some sel => Bool.not (selection_has_dep sel "root" "b")
  }

#[test]
def test_features_strong_enables_dep_and_weak_then_applies : Bool :=
  match resolved weak_fixture "root" ["weak", "strong"] true {
    Option.none => false,
    Option.some sel =>
      Bool.and (selection_has_dep sel "root" "b")
        (selection_has_feature sel "b" "f")
  }

#[test]
def test_features_weak_is_order_independent : Bool :=
  match resolved weak_fixture "root" ["strong", "weak"] true {
    Option.none => false,
    Option.some sel =>
      Bool.and (selection_has_dep sel "root" "b")
        (selection_has_feature sel "b" "f")
  }

#[test]
def test_features_unknown_request_is_error : Bool :=
  match Features.resolve optional_fixture "moon" ["nope"] false {
    Result.ok _ => false,
    Result.err _ => true
  }

#[test]
def test_features_dep_prefix_requires_optional : Bool :=
  let pkgs : List FeaturePackage := [
    fpkg "m"
      [fpair "default" List.empty, fpair "bad" ["dep:plain"]]
      [Pair.pair "plain" (fdep false List.empty true)]
  ] in
  match Features.resolve pkgs "m" ["bad"] true {
    Result.ok _ => false,
    Result.err _ => true
  }

#[test]
def test_features_plain_name_enables_optional_dep : Bool :=
  let pkgs : List FeaturePackage := [
    fpkg "m"
      [fpair "default" List.empty, fpair "use-crypto" ["crypto"]]
      [Pair.pair "crypto" (fdep true List.empty true)],
    fpkg "crypto" [fpair "default" List.empty] List.empty
  ] in
  match Features.resolve pkgs "m" ["use-crypto"] true {
    Result.ok sel => selection_has_dep sel "m" "crypto",
    Result.err _ => false
  }
