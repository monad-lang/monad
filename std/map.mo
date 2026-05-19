/// Key-value map type class. Types implementing Map provide ordered
/// key-value storage with insertion, lookup, and deletion.
class Map (M: Type -> Type -> Type) {
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
  BTreeMap.with_node ll
    (fn llk llv lll llr _ =>
      BTreeMap.create_node llk llv lll (BTreeMap.create_node root_key root_val llr right))
    (BTreeMap.create_node root_key root_val BTreeMap.empty right)

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
  BTreeMap.with_node rr
    (fn rrk rrv rrl rrr _ =>
      BTreeMap.create_node rrk rrv (BTreeMap.create_node root_key root_val left rrl) rrr)
    (BTreeMap.create_node root_key root_val left BTreeMap.empty)

/// Find the leftmost (minimum) node in the tree.
@[terminating]
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
@[terminating]
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
@[terminating]
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
@[terminating]
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
              (fn rk rv rl rr rh => BTreeMap.balance rk rv left rl)
              left)
          right)
    BTreeMap.empty

/// Instance: BTreeMap implements the Map type class.
instance [BOrd K] Map BTreeMap {
  def empty : BTreeMap K V := BTreeMap.empty

  @[terminating]
  def insert (key: K) (val: V) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.with_node m
      (fn k v left right h =>
        let insert_left : BTreeMap K V := Map.insert key val left in
        let insert_right : BTreeMap K V := Map.insert key val right in
        if BOrd.lt key k
        then BTreeMap.balance k v insert_left right
        else if BOrd.gt key k
        then BTreeMap.balance k v left insert_right
        else BTreeMap.node key val left right h)
      (BTreeMap.node key val BTreeMap.empty BTreeMap.empty 1)

  @[terminating]
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

  @[terminating]
  def delete (key: K) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.with_node m
      (fn k v left right h =>
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
                (fn rk rv rl rr rh => BTreeMap.balance rk rv left rl)
                left)
            right)
      BTreeMap.empty
}

/// ─── HashMap ────────────────────────────────────────────────

/// Compute bucket index (0–15) from a hash value.
def HashMap.bucket_of (hash: U64) : U64 := U64.mod hash 16u64

/// Fixed 16 buckets for the hash map.
type Buckets16 K V {
  buckets (
    b0 b1 b2 b3 b4 b5 b6 b7 
    b8 b9 b10 b11 b12 b13 b14 b15 
    : List (Pair K V))
}

/// Hash map type: 16-bucket chaining hash table.
type HashMap K V {
  map (Buckets16 K V)
}

/// 16 empty buckets.
def HashMap.empty_buckets {K V : Type} : Buckets16 K V :=
  Buckets16.buckets 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V)) 
    (List.empty : List (Pair K V)) (List.empty : List (Pair K V))

/// Look up the bucket at a given U64 index.
@[terminating]
def HashMap.get_bucket {K V : Type} (b: Buckets16 K V) (idx: U64) : List (Pair K V) :=
  match b {
    Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
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
      if U64.beq 14u64 idx then b14 else
      b15
  }

/// Return buckets with bucket at idx replaced by new_val.
@[terminating]
def HashMap.set_bucket {K V : Type} (b: Buckets16 K V) (idx: U64) (new_val: List (Pair K V)) : Buckets16 K V :=
  match b {
    Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 =>
      if U64.beq 0u64 idx then Buckets16.buckets new_val b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 1u64 idx then Buckets16.buckets b0 new_val b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 2u64 idx then Buckets16.buckets b0 b1 new_val b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 3u64 idx then Buckets16.buckets b0 b1 b2 new_val b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 4u64 idx then Buckets16.buckets b0 b1 b2 b3 new_val b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 5u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 new_val b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 6u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 new_val b7 b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 7u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 new_val b8 b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 8u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 new_val b9 b10 b11 b12 b13 b14 b15 else
      if U64.beq 9u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 new_val b10 b11 b12 b13 b14 b15 else
      if U64.beq 10u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 new_val b11 b12 b13 b14 b15 else
      if U64.beq 11u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 new_val b12 b13 b14 b15 else
      if U64.beq 12u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 new_val b13 b14 b15 else
      if U64.beq 13u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 new_val b14 b15 else
      if U64.beq 14u64 idx then Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 new_val b15 else
      Buckets16.buckets b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 new_val
  }

/// Instance: HashMap implements the Map type class using hashing + ordering-based equality.
/// NOTE: uses BOrd K instead of BEq K due to evaluator instance resolution limitation.
/// The evaluator's resolve_class_method_instance picks the first registered instance
/// (BOrd I64 is correctly first for I64 keys, but BEq Bool is first for BEq, producing
/// wrong instance when abstract K is concrete I64 at runtime).
instance [Hashable K, BOrd K] Map HashMap {
  def empty : HashMap K V := HashMap.map HashMap.empty_buckets

  @[terminating]
  def insert (key: K) (val: V) (m: HashMap K V) : HashMap K V :=
    match m {
      HashMap.map buckets =>
        let idx : U64 := HashMap.bucket_of (Hashable.hash key) in
        let bucket : List (Pair K V) := HashMap.get_bucket buckets idx in
        let new_bucket : List (Pair K V) :=
          HashMap.bucket_insert BOrd.lt BOrd.gt key val bucket in
        HashMap.map (HashMap.set_bucket buckets idx new_bucket)
    }

  @[terminating]
  def lookup (key: K) (m: HashMap K V) : Option V :=
    match m {
      HashMap.map buckets =>
        let idx : U64 := HashMap.bucket_of (Hashable.hash key) in
        let bucket : List (Pair K V) := HashMap.get_bucket buckets idx in
        HashMap.bucket_lookup BOrd.lt BOrd.gt key bucket
    }

  @[terminating]
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

/// Insert (key, val) into a single bucket, replacing existing key if present.
/// Equality check: not (lt a b) && not (gt a b)  (equivalent to a == b for total orders).
@[terminating]
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

/// Look up a key in a single bucket.
@[terminating]
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
@[terminating]
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
