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

/// Instance: BTreeMap implements the Map type class.
/// NOTE: insert/lookup/delete require BOrd constraint propagation
/// for type variables in instance method bodies (compiler fix needed).
/// Full implementations exist in the BTreeMap module.
instance [BOrd K] Map BTreeMap {
  def empty : BTreeMap K V := BTreeMap.empty

  def insert (key: K) (val: V) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.empty

  def lookup (key: K) (m: BTreeMap K V) : Option V :=
    Option.none

  def delete (key: K) (m: BTreeMap K V) : BTreeMap K V :=
    BTreeMap.empty
}
