/// Key-value map type class. Types implementing Map provide ordered
/// key-value storage with insertion, lookup, and deletion.
///
/// `:= HashMap` -- a declared default carrier, matching
/// `class FromListLiteral (L : Type -> Type := List)`'s own convention
/// -- so a NULLARY call like `Map.empty` (no args to infer a carrier
/// from at all) can still resolve via
/// `resolve_class_method_call_d4_default_carrier` (`lang/scope.mo`)
/// instead of giving up. Confirmed via `bootstrap compile lang/main.mo
/// monad`: `lang/module.mo`'s `module_scope_cache_empty`'s own struct-
/// literal field `entries := Map.empty` (declared field type `HashMap
/// ModulePath ScopeData`, `ModuleScopeCache`) hit exactly this -- that
/// caller has since been deleted as dead code, but the gap it found is
/// real and this default is what closes it --
/// `HashMap` is already this codebase's own preferred `Map` instance
/// (see `filter_reachable_decls`'s own doc comment on why), so it's the
/// correct default here too.
class Map (M: (K : Type) -> (V : Type) -> Type := HashMap) {
  def empty : M K V
  def insert (key: K) (val: V) (m: M K V) : M K V
  def lookup (key: K) (m: M K V) : Option V
  def delete (key: K) (m: M K V) : M K V
}

/// Balanced binary search tree (AVL) key-value map.
type BTreeMap K V {
  empty,
  node (key: K) (val: V) (left: BTreeMap K V) (right: BTreeMap K V) (height: I64)
}

def BTreeMap.beq [BEq K, BEq V] (a b : BTreeMap K V) : Bool :=
  BTreeMap.fold (fn r ka va =>
    r && Map.lookup ka b == some va
  ) true a

instance [BEq K, BEq V] BEq BTreeMap K V {
  def beq (a b : BTreeMap K V) : Bool := BTreeMap.beq a b
}

/// Eliminator: apply a function if the tree is a node, otherwise return default.
def BTreeMap.with_node (m: BTreeMap K V) (f: K -> V -> BTreeMap K V -> BTreeMap K V -> I64 -> A) (default: A) : A :=
  match m {
    BTreeMap.node k v l r h => f k v l r h,
    BTreeMap.empty => default
  }

/// Return the height of a tree. Empty tree has height 0.
def BTreeMap.height_of (m: BTreeMap K V) : I64 :=
  BTreeMap.with_node m (fn k v l r h => h) 0

/// Create a node, computing the height from children.
def BTreeMap.create_node {K V : Type} (key: K) (val: V) (left: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  let lh := BTreeMap.height_of left in
  let rh := BTreeMap.height_of right in
  if I64.gt lh rh
  then BTreeMap.node key val left right (lh + 1)
  else BTreeMap.node key val left right (rh + 1)

/// Balance a key-value pair with left and right children.
/// Detects AVL imbalance and applies rotations inline.
def BTreeMap.balance {K V : Type} (key: K) (val: V) (left: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  let lh := BTreeMap.height_of left in
  let rh := BTreeMap.height_of right in
  if I64.gt lh (rh + 1)
  then BTreeMap.balance_left_heavy key val left right
  else if I64.gt rh (lh + 1)
  then BTreeMap.balance_right_heavy key val left right
  else BTreeMap.create_node key val left right

/// Handle left-heavy imbalance: check children heights and apply LL or LR rotation.
def BTreeMap.balance_left_heavy {K V : Type} (key: K) (val: V) (left: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node left
    (fn lk lv ll lr _ =>
      let llh := BTreeMap.height_of ll in
      let lrh := BTreeMap.height_of lr in
      if I64.gt lrh llh
      then BTreeMap.rotate_lr key val lk lv ll lr right
      else BTreeMap.rotate_ll key val lk lv ll lr right)
    (BTreeMap.create_node key val left right)

/// Left-right double rotation.
def BTreeMap.rotate_lr {K V : Type} (root_key: K) (root_val: V) (l_key: K) (l_val: V) (ll: BTreeMap K V) (lr: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node lr
    (fn lrk lrv lrl lrr _ =>
      let new_left := BTreeMap.create_node l_key l_val ll lrl in
      BTreeMap.create_node lrk lrv new_left (BTreeMap.create_node root_key root_val lrr right))
    (BTreeMap.create_node root_key root_val (BTreeMap.create_node l_key l_val ll BTreeMap.empty) right)

/// Left-left single rotation.
def BTreeMap.rotate_ll {K V : Type} (root_key: K) (root_val: V) (l_key: K) (l_val: V) (ll: BTreeMap K V) (lr: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.create_node l_key l_val ll (BTreeMap.create_node root_key root_val lr right)

/// Handle right-heavy imbalance: check children heights and apply RR or RL rotation.
def BTreeMap.balance_right_heavy {K V : Type} (key: K) (val: V) (left: BTreeMap K V) (right: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node right
    (fn rk rv rl rr _ =>
      let rlh := BTreeMap.height_of rl in
      let rrh := BTreeMap.height_of rr in
      if I64.gt rlh rrh
      then BTreeMap.rotate_rl key val left rk rv rl rr
      else BTreeMap.rotate_rr key val left rk rv rl rr)
    (BTreeMap.create_node key val left right)

/// Right-left double rotation.
def BTreeMap.rotate_rl {K V : Type} (root_key: K) (root_val: V) (left: BTreeMap K V) (r_key: K) (r_val: V) (rl: BTreeMap K V) (rr: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node rl
    (fn rlk rlv rll rlr _ =>
      let new_right := BTreeMap.create_node r_key r_val rlr rr in
      BTreeMap.create_node rlk rlv (BTreeMap.create_node root_key root_val left rll) new_right)
    (BTreeMap.create_node root_key root_val left (BTreeMap.create_node r_key r_val BTreeMap.empty rr))

/// Right-right single rotation.
def BTreeMap.rotate_rr {K V : Type} (root_key: K) (root_val: V) (left: BTreeMap K V) (r_key: K) (r_val: V) (rl: BTreeMap K V) (rr: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.create_node r_key r_val (BTreeMap.create_node root_key root_val left rl) rr

/// Find the leftmost (minimum) node in the tree.
#[terminating]
def BTreeMap.min_node (m: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node m
    (fn k v left right h =>
      BTreeMap.with_node left
        (fn lk lv ll lr lh => BTreeMap.min_node left)
        m)
    BTreeMap.empty

/// Fold over the map in ascending key order.
def BTreeMap.fold (f: A -> K -> V -> A) (init: A) (m: BTreeMap K V) : A :=
  match m {
    BTreeMap.empty => init,
    BTreeMap.node k v left right _ =>
      let left_result := BTreeMap.fold f init left in
      let current_result := f left_result k v in
      BTreeMap.fold f current_result right
  }

/// Convert the map to a list of (key, value) pairs in ascending key order.
def BTreeMap.to_list {K V : Type} (m: BTreeMap K V) : List (Pair K V) :=
  BTreeMap.to_list_asc m (List.empty : List (Pair K V))

def BTreeMap.to_list_asc (m: BTreeMap K V) (acc: List (Pair K V)) : List (Pair K V) :=
  match m {
    BTreeMap.empty => acc,
    BTreeMap.node k v left right _ =>
      let acc1 := BTreeMap.to_list_asc right acc in
      let acc2 := List.cons (Pair.pair k v) acc1 in
      BTreeMap.to_list_asc left acc2
  }

/// Recursive insert helper. Takes comparison functions explicitly to avoid
/// needing type class constraints on recursive self-calls.
/// NOTE: this function is ready for use but requires compiler support for
/// evaluating class method references (BOrd.lt/BOrd.gt) passed as arguments
/// from constrained instance bodies.
#[terminating]
def BTreeMap.insert_loop {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (val: V) (m: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node m
    (fn k v left right h =>
      let insert_left : BTreeMap K V := BTreeMap.insert_loop lt gt key val left in
      let insert_right : BTreeMap K V := BTreeMap.insert_loop lt gt key val right in
      if lt key k
      then BTreeMap.balance k v insert_left right
      else if gt key k
      then BTreeMap.balance k v left insert_right
      else BTreeMap.node key val left right h)
    (BTreeMap.node key val BTreeMap.empty BTreeMap.empty 1)

/// Recursive lookup helper.
#[terminating]
def BTreeMap.lookup_loop {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (m: BTreeMap K V) : Option V :=
  match m {
    BTreeMap.empty => Option.none,
    BTreeMap.node k v left right _ =>
      if lt key k
      then BTreeMap.lookup_loop lt gt key left
      else if gt key k
      then BTreeMap.lookup_loop lt gt key right
      else Option.some v
  }

/// Recursive delete helper.
#[terminating]
def BTreeMap.delete_loop {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (m: BTreeMap K V) : BTreeMap K V :=
  BTreeMap.with_node m
    (fn k v left right h =>
      let delete_left : BTreeMap K V := BTreeMap.delete_loop lt gt key left in
      let delete_right : BTreeMap K V := BTreeMap.delete_loop lt gt key right in
      if lt key k
      then BTreeMap.balance k v delete_left right
      else if gt key k
      then BTreeMap.balance k v left delete_right
      else
        BTreeMap.with_node left
          (fn lk lv ll lr lh =>
            BTreeMap.with_node right
              (fn rk rv rl rr rh =>
                BTreeMap.with_node (BTreeMap.min_node right)
                  (fn mk mv _ _ _ =>
                    BTreeMap.balance mk mv left (BTreeMap.delete_loop lt gt mk right))
                  right)
              left)
          right)
    BTreeMap.empty

/// Instance: BTreeMap implements the Map type class.
instance [BOrd K] Map BTreeMap {
  def empty : BTreeMap K V := BTreeMap.empty

  // `with_node`'s callback params are explicitly typed (`left`/`right :
  // BTreeMap K V`) -- needed so `lang.scope`'s syntactic dictionary-
  // passing pass (`resolve_class_call_term`'s `Term.lam` case, the same
  // one that already registers any OTHER typed lambda/let param) can
  // see `left`/`right`'s own carrier when resolving the SELF-RECURSIVE
  // `Map.insert key val left`/`right` calls below. Confirmed load-
  // bearing via `examples/json.mo`'s `Map.insert` on a real `BTreeMap`
  // compiling to a hard "no instance found" failure without this. Typed
  // `fn` params inside a function-call argument position (this
  // `with_node` call) needed a separate self-hosted-parser fix first
  // (`lambda_dispatch`/`lambda_typed_params`, `lang/parser.mo`) --
  // before that, this exact annotation broke self-hosted parsing
  // outright.
  #[terminating]
  def insert (key: K) (val: V) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.with_node m
      (fn (k : K) (v : V) (left : BTreeMap K V) (right : BTreeMap K V) (h : I64) =>
        let insert_left : BTreeMap K V := Map.insert key val left in
        let insert_right : BTreeMap K V := Map.insert key val right in
        if BOrd.lt key k
        then BTreeMap.balance k v insert_left right
        else if BOrd.gt key k
        then BTreeMap.balance k v left insert_right
        else BTreeMap.node key val left right h)
      (BTreeMap.node key val BTreeMap.empty BTreeMap.empty 1)

  #[terminating]
  def lookup (key: K) (m: BTreeMap K V) : Option V :=
    match m {
      BTreeMap.empty => Option.none,
      BTreeMap.node k v left right _ =>
        if BOrd.lt key k
        then Map.lookup key left
        else if BOrd.gt key k
        then Map.lookup key right
        else Option.some v
    }

  // Same rationale as `insert`'s own doc comment above -- `left`/`right`
  // need real declared types for the self-recursive `Map.delete` calls
  // (both directly below and nested inside the `else` branch's own
  // `with_node` calls, which still see this outer `right` in scope) to
  // resolve their own `Map` instance dispatch.
  #[terminating]
  def delete (key: K) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.with_node m
      (fn (k : K) (v : V) (left : BTreeMap K V) (right : BTreeMap K V) (h : I64) =>
        let delete_left : BTreeMap K V := Map.delete key left in
        let delete_right : BTreeMap K V := Map.delete key right in
        if BOrd.lt key k
        then BTreeMap.balance k v delete_left right
        else if BOrd.gt key k
        then BTreeMap.balance k v left delete_right
        else
          BTreeMap.with_node left
            (fn lk lv ll lr lh =>
              BTreeMap.with_node right
                (fn rk rv rl rr rh =>
                  BTreeMap.with_node (BTreeMap.min_node right)
                    (fn mk mv _ _ _ =>
                      BTreeMap.balance mk mv left (Map.delete mk right))
                    right)
                left)
            right)
      BTreeMap.empty
}

/// ─── HashMap ────────────────────────────────────────────────

/// Compute bucket index (0-255) from a hash value.
///
/// 256, not 16. The table is two LEVELS of the same 16-way dispatch
/// (`Bucket16` below), so widening cost no new dispatch code -- and the
/// old 16 was badly under-provisioned for how this codebase actually
/// uses `HashMap`: the compiler keeps ~4,200 def names and ~2,700
/// reachability entries in one map, which at 16 buckets is ~260 entries
/// per bucket, and `bucket_lookup_eq` scans a bucket LINEARLY. That made
/// every lookup ~130 key comparisons on the hottest paths in the
/// backend. At 256 the same maps sit at ~16 per bucket.
def HashMap.bucket_of (hash: U64) : U64 := U64.mod hash 256u64

/// One level of 16-way dispatch, generic in what a slot holds.
///
/// Generic in `P` specifically so it can nest: a `HashMap`'s table is
/// `Bucket16 (Bucket16 (List (Pair K V)))`, which is 256 buckets built
/// from ONE 16-arm dispatch written once, rather than a 256-field
/// constructor and two 256-arm chains.
type Bucket16 P {
  buckets (
    b0 b1 b2 b3 b4 b5 b6 b7
    b8 b9 b10 b11 b12 b13 b14 b15
    : P)
}

/// Hash map type: 256-bucket chaining hash table, as 16x16.
type HashMap K V {
  map (Bucket16 (Bucket16 (List (Pair K V))))
}

/// Every slot, in index order -- the basis for the whole-table folds
/// (`to_list`, `is_empty`) that used to be written out 16 ways.
def Bucket16.to_list {P : Type} (b : Bucket16 P) : List P :=
  match b {
    Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
  }

/// All 16 slots set to the same value.
def Bucket16.replicate {P : Type} (e : P) : Bucket16 P :=
  Bucket16.buckets e e e e e e e e e e e e e e e e

/// Slot-wise combine of two levels -- what `merge_buckets` is.
def Bucket16.map2 {P : Type} (f : P -> P -> P) (x : Bucket16 P) (y : Bucket16 P) : Bucket16 P :=
  match x {
    Bucket16.buckets a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 =>
      match y {
        Bucket16.buckets c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 =>
          Bucket16.buckets
            (f a0 c0) (f a1 c1) (f a2 c2) (f a3 c3)
            (f a4 c4) (f a5 c5) (f a6 c6) (f a7 c7)
            (f a8 c8) (f a9 c9) (f a10 c10) (f a11 c11)
            (f a12 c12) (f a13 c13) (f a14 c14) (f a15 c15)
      }
  }

/// 16 empty buckets.
def HashMap.empty_buckets {K V : Type} : Bucket16 (Bucket16 (List (Pair K V))) :=
  Bucket16.replicate (Bucket16.replicate (List.empty : List (Pair K V)))

/// One 16-way step per level. The index is a flat 0-255 so that every
/// caller -- `str_map_*` (`lang/codegen/util.mo`), `modpath_map_*` and
/// `alias_map_*` (`lang/scope.mo`) -- keeps working unchanged against
/// `bucket_of`/`get_bucket`/`set_bucket`; the two-level shape is an
/// implementation detail of this file.
def Bucket16.get {P : Type} (b : Bucket16 P) (idx : U64) : P :=
  match b {
    Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
      if U64.beq 0u64 idx then b0 else
      if U64.beq 1u64 idx then b1 else
      if U64.beq 2u64 idx then b2 else
      if U64.beq 3u64 idx then b3 else
      if U64.beq 4u64 idx then b4 else
      if U64.beq 5u64 idx then b5 else
      if U64.beq 6u64 idx then b6 else
      if U64.beq 7u64 idx then b7 else
      if U64.beq 8u64 idx then b8 else
      if U64.beq 9u64 idx then b9 else
      if U64.beq 10u64 idx then b10 else
      if U64.beq 11u64 idx then b11 else
      if U64.beq 12u64 idx then b12 else
      if U64.beq 13u64 idx then b13 else
      if U64.beq 14u64 idx then b14 else b15
  }

def Bucket16.set {P : Type} (b : Bucket16 P) (idx : U64) (v : P) : Bucket16 P :=
  match b {
    Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
      if U64.beq 0u64 idx then Bucket16.buckets v b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 1u64 idx then Bucket16.buckets b0 v b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 2u64 idx then Bucket16.buckets b0 b1 v b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 3u64 idx then Bucket16.buckets b0 b1 b2 v b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 4u64 idx then Bucket16.buckets b0 b1 b2 b3 v b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 5u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 v b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 6u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 v b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 7u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 v b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 8u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 v b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 9u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 v b10 b11 b12 b13 b14 b15 else
      if U64.beq 10u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 v b11 b12 b13 b14 b15 else
      if U64.beq 11u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 v b12 b13 b14 b15 else
      if U64.beq 12u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 v b13 b14 b15 else
      if U64.beq 13u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 v b14 b15 else
      if U64.beq 14u64 idx then Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 v b15 else
      Bucket16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 v
  }

def HashMap.get_bucket {K V : Type} (b: Bucket16 (Bucket16 (List (Pair K V)))) (idx: U64) : List (Pair K V) :=
  Bucket16.get (Bucket16.get b (U64.div idx 16u64)) (U64.mod idx 16u64)

def HashMap.set_bucket {K V : Type} (b: Bucket16 (Bucket16 (List (Pair K V)))) (idx: U64) (new_val: List (Pair K V)) : Bucket16 (Bucket16 (List (Pair K V))) :=
  let hi : U64 := U64.div idx 16u64 in
  let lo : U64 := U64.mod idx 16u64 in
  Bucket16.set b hi (Bucket16.set (Bucket16.get b hi) lo new_val)

/// Instance: HashMap implements the Map type class using hashing + ordering-based equality.
/// NOTE: uses BOrd K instead of BEq K due to evaluator instance resolution limitation.
/// The evaluator's resolve_class_method_instance picks the first registered instance
/// (BOrd I64 is correctly first for I64 keys, but BEq Bool is first for BEq, producing
/// wrong instance when abstract K is concrete I64 at runtime).
instance [Hashable K, BOrd K] Map HashMap {
  def empty : HashMap K V := HashMap.map HashMap.empty_buckets

  #[terminating]
  def insert (key: K) (val: V) (m: HashMap K V) : HashMap K V :=
    match m {
      HashMap.map buckets =>
        let idx : U64 := HashMap.bucket_of (Hashable.hash key) in
        let bucket : List (Pair K V) := HashMap.get_bucket buckets idx in
        let new_bucket : List (Pair K V) :=
          HashMap.bucket_insert BOrd.lt BOrd.gt key val bucket in
        HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

  #[terminating]
  def lookup (key: K) (m: HashMap K V) : Option V :=
    match m {
      HashMap.map buckets =>
        let idx : U64 := HashMap.bucket_of (Hashable.hash key) in
        let bucket : List (Pair K V) := HashMap.get_bucket buckets idx in
        HashMap.bucket_lookup BOrd.lt BOrd.gt key bucket
    }

  #[terminating]
  def delete (key: K) (m: HashMap K V) : HashMap K V :=
    match m {
      HashMap.map buckets =>
        let idx : U64 := HashMap.bucket_of (Hashable.hash key) in
        let bucket : List (Pair K V) := HashMap.get_bucket buckets idx in
        let new_bucket : List (Pair K V) :=
          HashMap.bucket_delete BOrd.lt BOrd.gt key bucket in
        HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }
}

def HashMap.bucket_insert {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (val: V) (bucket: List (Pair K V)) : List (Pair K V) :=
  match bucket {
    List.empty => List.cons (Pair.pair key val) List.empty,
    List.cons pair rest =>
      match pair {
        Pair.pair k v =>
          if Bool.not (lt key k) && Bool.not (gt key k)
          then List.cons (Pair.pair key val) rest
          else List.cons pair (HashMap.bucket_insert lt gt key val rest)
      }
  }

/// Equality-predicate variants of `bucket_insert`/`bucket_lookup`.
///
/// The lt/gt versions above use `!lt(k1,k2) && !gt(k1,k2)` purely as an
/// EQUALITY test -- the chain is not kept sorted (insert appends at the
/// end; only an existing equal key is replaced in place), so ordering is
/// never relied on. That costs TWO comparator calls per chain step, and
/// for a key whose comparator renders a string (`lang/scope.mo`'s
/// `modpath_lt`/`modpath_gt` both call `show_module_path`, which rebuilds
/// the path via `List.map` + `intercalate`) that is four string
/// constructions per step. These variants take a single `eq` instead.
#[terminating]
def HashMap.bucket_insert_eq {K V : Type} (eq: K -> K -> Bool) (key: K) (val: V) (bucket: List (Pair K V)) : List (Pair K V) :=
  match bucket {
    List.empty => List.cons (Pair.pair key val) List.empty,
    List.cons pair rest =>
      match pair {
        Pair.pair k v =>
          if eq key k
          then List.cons (Pair.pair key val) rest
          else List.cons pair (HashMap.bucket_insert_eq eq key val rest)
      }
  }

#[terminating]
def HashMap.bucket_lookup_eq {K V : Type} (eq: K -> K -> Bool) (key: K) (bucket: List (Pair K V)) : Option V :=
  match bucket {
    List.empty => Option.none,
    List.cons pair rest =>
      match pair {
        Pair.pair k v =>
          if eq key k then Option.some v
          else HashMap.bucket_lookup_eq eq key rest
      }
  }

/// Look up a key in a single bucket.
#[terminating]
def HashMap.bucket_lookup {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (bucket: List (Pair K V)) : Option V :=
  match bucket {
    List.empty => Option.none,
    List.cons pair rest =>
      match pair {
        Pair.pair k v =>
          if Bool.not (lt key k) && Bool.not (gt key k)
          then Option.some v
          else HashMap.bucket_lookup lt gt key rest
      }
  }

/// Delete a key from a single bucket.
#[terminating]
def HashMap.bucket_delete {K V : Type} (lt: K -> K -> Bool) (gt: K -> K -> Bool) (key: K) (bucket: List (Pair K V)) : List (Pair K V) :=
  match bucket {
    List.empty => List.empty,
    List.cons pair rest =>
      match pair {
        Pair.pair k v =>
          if Bool.not (lt key k) && Bool.not (gt key k)
          then rest
          else List.cons pair (HashMap.bucket_delete lt gt key rest)
      }
  }

/// Concatenate two `List (Pair K V)`s — a local helper rather than
/// reaching for the prelude's own `List.append` (curried differently,
/// per `lang/scope.mo`'s/`lang/module.mo`'s own local `list_append`
/// helpers and their doc comments).
#[terminating]
def HashMap.concat_lists {K V : Type} (a : List (Pair K V)) (b : List (Pair K V)) : List (Pair K V) :=
  match a {
    List.empty => b,
    List.cons x rest => List.cons x (HashMap.concat_lists rest b)
  }

#[terminating]
def HashMap.concat_all {K V : Type} (lists : List (List (Pair K V))) : List (Pair K V) :=
  match lists {
    List.empty => List.empty,
    List.cons hd rest => HashMap.concat_lists hd (HashMap.concat_all rest)
  }

/// Convert the map to a list of (key, value) pairs — unlike
/// `BTreeMap.to_list`, in NO particular order (buckets are visited
/// 0..15, each bucket's own chain in insertion order, which has no
/// relationship to key order for a hash table).
def HashMap.to_list {K V : Type} (m: HashMap K V) : List (Pair K V) :=
  match m {
    HashMap.map outer => HashMap.concat_inners (Bucket16.to_list outer)
  }

/// Flatten one outer level: each slot is itself 16 buckets.
def HashMap.concat_inners {K V : Type} (inners : List (Bucket16 (List (Pair K V)))) : List (Pair K V) :=
  match inners {
    List.empty => List.empty,
    List.cons inner rest =>
      HashMap.concat_lists (HashMap.concat_all (Bucket16.to_list inner))
        (HashMap.concat_inners rest)
  }

/// Emptiness without walking entries. Recursive over the two levels
/// rather than two 8-wide `&&` chains: the chain-length rule that shaped
/// the old `buckets_all_empty_lo`/`_hi` pair does not scale to 256, and
/// the recursion short-circuits on the first non-empty bucket anyway.
/// Kept cheap because `lang/module.mo`'s `merge_scope_data` uses it to
/// skip a `to_list`-then-reinsert merge entirely.
def HashMap.lists_all_empty {K V : Type} (ls : List (List (Pair K V))) : Bool :=
  match ls {
    List.empty => true,
    List.cons l rest => if List.is_empty l then HashMap.lists_all_empty rest else false
  }

def HashMap.inners_all_empty {K V : Type} (inners : List (Bucket16 (List (Pair K V)))) : Bool :=
  match inners {
    List.empty => true,
    List.cons inner rest =>
      if HashMap.lists_all_empty (Bucket16.to_list inner)
      then HashMap.inners_all_empty rest
      else false
  }

def HashMap.is_empty {K V : Type} (m: HashMap K V) : Bool :=
  match m {
    HashMap.map outer => HashMap.inners_all_empty (Bucket16.to_list outer)
  }

/// NOTE: a generic `HashMap.insert_all [Hashable K, BOrd K] (pairs: List
/// (Pair K V)) (acc: HashMap K V) : HashMap K V` (fold-inserting `pairs`
/// into `acc`, the natural building block for a `HashMap.merge`) was
/// tried here and removed — it doesn't work. This is a *broader* form of
/// the limitation `HashMap`'s own `instance` block already documents for
/// `Map.insert` specifically: from a standalone `[Constraint]`-annotated
/// function (as opposed to directly inside an `instance ... { }` body),
/// EVERY class-method call misbehaves, not just generic `Map` dispatch —
/// confirmed empirically by bisection:
///   - Calling generic `Map.insert k v acc` from such a function raises
///     `unresolved global: Map.insert` at runtime.
///   - Calling `HashMap`'s own concrete bucket primitives instead
///     (`Hashable.hash k`, `BOrd.lt`/`BOrd.gt` — the exact calls the
///     `Map HashMap` instance's own `insert` body makes, and the
///     workaround that fixed the above) still fails, but differently:
///     a function no more complex than `match acc { HashMap.map _ =>
///     true }` plus one `Hashable.hash k` call in the same body returns
///     an under-applied `Closure` instead of its declared `Bool`, i.e.
///     the call site ends up with fewer arguments than the compiled
///     function expects — apparently from however constraint
///     dictionaries get threaded through the class-method calls, not
///     from `match` itself (a `[Constraint]`-annotated function that
///     never calls a class method, e.g. `qux` in the bisection, matches
///     `acc` against `HashMap.map _` with no issue).
///   - The exact same code, monomorphic (no `[Constraint]` list, all
///     types concrete — e.g. specialized to a single key type instead of
///     generic `K`) works with no issue, calling ordinary `Map.insert`/
///     `Map.lookup` exactly like `bench/scope_lookup.mo`'s
///     `hashmap_build`/`hashmap_lookup_range` already do successfully.
/// Net: this evaluator's class-method dispatch is reliable inside
/// `instance` bodies and inside monomorphic call sites, not inside
/// generic `[Constraint]`-annotated helper functions. Callers needing a
/// `HashMap` fold/merge should write a monomorphic version specialized
/// to their concrete key/value types (see `lang/scope.mo`'s
/// `merge_def_refs`) rather than a generic one here.
///
/// `HashMap.merge_buckets` just below takes a different, better
/// approach for the actual real-world need (`lang/module.mo`'s
/// `merge_scope_data`, merging `ScopeData.def_refs`) — it needs no
/// `[Constraint]` list at all, so it sidesteps this whole limitation
/// rather than working around it.

/// Merge two `HashMap`s bucket-by-bucket, WITHOUT re-hashing any key —
/// safe specifically because both sides already used the SAME hash
/// function to place their entries, so a key that landed in bucket `i`
/// on one side always lands in bucket `i` on the other too. `m1`'s
/// entries come FIRST in each merged bucket's list, so `m1` wins over
/// `m2` on a duplicate key (matches `HashMap.bucket_lookup`'s own
/// head-first linear scan — same "first argument wins" precedence
/// `merge_scope_data`/`list_append`'s own callers already rely on).
/// Needs no `[Hashable K, BOrd K]` constraint (unlike a `to_list`+
/// refold merge through `Map.insert`) since it never calls
/// `Hashable.hash`/`BOrd.lt`/`BOrd.gt` — just 16 `List.append` calls,
/// one per bucket, however many entries each side holds. Measurably
/// cheaper than the `to_list`+refold pattern this replaces in
/// `lang/module.mo`'s `merge_scope_data` (that pattern rebuilds the
/// WHOLE combined map via one `Map.insert`-equivalent call per entry,
/// re-walking/reallocating a bucket on every single insert; this does a
/// fixed 16 bucket-pair appends regardless of N) — see AGENTS.md's
/// performance section for the measured before/after.
def HashMap.merge_buckets {K V : Type} (m1: HashMap K V) (m2: HashMap K V) : HashMap K V :=
  match m1 {
    HashMap.map a =>
      match m2 {
        HashMap.map b =>
          HashMap.map (Bucket16.map2 (Bucket16.map2 List.append) a b)
      }
  }

