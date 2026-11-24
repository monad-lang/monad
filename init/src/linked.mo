/// A linear singly-linked list: pointer swapping with no raw pointer.
///
/// The view-types library (`init/src/view.mo`) gives a linear handle whose only
/// operations consume it and return it. This module uses that discipline to
/// build a *mutable* list: every node is a
/// `Slot Full (Pair A (Link A))` — a heap cell holding one element and the
/// handle to the next node — and every operation that changes the list does it
/// by taking a node's payload out and putting a new payload back into the SAME
/// handle (`Slot.take` / `Slot.fill`). The heap object never moves; only the
/// pointer it holds changes. That is the classic in-place relink, spelled with
/// a typed handle instead of an address.
///
/// ## What the handles make impossible
///
/// - A `Link` has no `Copy`/`Clone` instance and a `Slot` has no `Copy`, so a
///   node handle cannot be duplicated: two cursors into one list are
///   untypable. `reverse` and `swap_adjacent` below rely on this — the node
///   they are relinking is the only handle to that cell.
/// - Every `Slot Full` is emptied by `Slot.take` before anything else can use
///   it, and every emptied handle is either refilled or freed on the same path,
///   so a node cannot be read after its cell is released, and a second
///   `Slot.take` of the same node cannot be written.
/// - There is no arithmetic on a handle and no way to forge one: the only
///   producers are `Slot.new`/`Slot.empty`, and the only way to reach a node is
///   to follow the link of the node you already own. "Pointer arithmetic" here
///   is exactly "walk a link you hold".
///
/// ## Leaks, not dangling
///
/// Dropping a `Link` (matching it and returning something else) leaks its
/// nodes, which the safety invariants permit (P8: leaks are permitted, dangling
/// views are not). Every public operation below consumes what it is given and
/// returns a list that owns the surviving handles, so the common flows do not
/// leak.
///
/// ## Limits
///
/// Not expressible in v1, by design: two cursors into one list (needs proofs
/// over a *segment*, which `plans/type-system/view-types.md` defers); a
/// shared/read-only walk (`Shared` of a linear payload is rejected, P11); and
/// closure capture of a list handle (P10 — a closure may run many times, and
/// every operation here uses `let`/`match` or a def-level continuation
/// instead).
///
/// ## Why the `let` binders are annotated
///
/// `let p <- Slot.take s` infers `p`'s type from the callee's DECLARED `IO`
/// payload, which still carries `Slot.take`'s own type variable (`Pair A (Slot
/// Empty A)`) rather than the instantiated `Pair (Pair A (Link A)) ...`. A
/// binder named `A` then resolves against this module's `A` and the flow stops
/// type-checking. Annotating the binder (the same workaround
/// `init/src/view_tests.mo` uses for `Slot.empty`) pins the instantiation.
use init::view {Empty, Full, Slot}

/// The handle to the first node, or the end of the list.
///
/// `#[linear]`, not merely affine: the list *contains* linear node handles, and
/// a value that owns linear handles is linear itself. Marking it is what makes
/// the containment visible to the checker's rules — in particular `Shared.of l`
/// is rejected (P11, a re-readable container could hand out two cursors) and a
/// dropped list is an error rather than a leak. It is also the honest reading:
/// "walked exactly once" is the whole contract of the type.
#[linear]
pub type Link A {
    nil,
    node (Slot Full (Pair A (Link A))),
}

// ─── Construction ───────────────────────────────────────────────────
//
// One helper per step: a `let x <- ...` inside a match arm is a recorded
// checker trap, so each continuation gets its own def (the shape
// `init/src/view_tests.mo` uses).

/// Build a list from a `List`. The last element is allocated first, and each
/// earlier element points at the list built so far.
pub def Linked.from_list (xs : List A) : IO (Link A) :=
    match xs {
        List.empty => IO.pure Link.nil,
        List.cons x rest => from_list_then x rest,
    }

#[terminating]
def from_list_then (x : A) (rest : List A) : IO (Link A) := do {
    let tail <- Linked.from_list rest;
    let s : Slot Full (Pair A (Link A)) <- Slot.new (Pair.pair x tail);
    IO.pure (Link.node s)
}

// ─── Folding back out ───────────────────────────────────────────────

/// Walk the list front to back, consuming it: each node's payload is taken,
/// its now-empty handle freed, and its element copied into the result.
pub def Linked.to_list (l : Link A) : IO (List A) :=
    match l {
        Link.nil => IO.pure List.empty,
        Link.node s => to_list_node s,
    }

#[terminating]
def to_list_node (s : Slot Full (Pair A (Link A))) : IO (List A) := do {
    let p : Pair (Pair A (Link A)) (Slot Empty (Pair A (Link A))) <- Slot.take s;
    match p {
        Pair.pair payload empty => to_list_arm payload empty,
    }
}

def to_list_arm (payload : Pair A (Link A)) (empty : Slot Empty (Pair A (Link A))) : IO (List A) :=
    match payload {
        Pair.pair x rest => to_list_free x rest empty,
    }

#[terminating]
def to_list_free (x : A) (rest : Link A) (empty : Slot Empty (Pair A (Link A))) : IO (List A) := do {
    let _ <- Slot.free empty;
    let xs <- Linked.to_list rest;
    IO.pure (List.cons x xs)
}

/// How many nodes the list holds. Same walk as `to_list`, without building
/// the result list.
pub def Linked.length (l : Link A) : IO I64 :=
    match l {
        Link.nil => IO.pure 0i64,
        Link.node s => length_node s,
    }

#[terminating]
def length_node (s : Slot Full (Pair A (Link A))) : IO I64 := do {
    let p : Pair (Pair A (Link A)) (Slot Empty (Pair A (Link A))) <- Slot.take s;
    match p {
        Pair.pair payload empty => length_arm payload empty,
    }
}

def length_arm (payload : Pair A (Link A)) (empty : Slot Empty (Pair A (Link A))) : IO I64 :=
    match payload {
        Pair.pair _ rest => length_free rest empty,
    }

#[terminating]
def length_free (rest : Link A) (empty : Slot Empty (Pair A (Link A))) : IO I64 := do {
    let _ <- Slot.free empty;
    let n <- Linked.length rest;
    IO.pure (I64.add n 1i64)
}

// ─── Pointer swapping ───────────────────────────────────────────────

/// Reverse in place: each node is put back into its OWN handle, now pointing
/// at the reversed prefix. The heap cells are untouched; their links are
/// swapped as the cursor passes through them.
pub def Linked.reverse (l : Link A) : IO (Link A) :=
    Linked.reverse_go l Link.nil

def Linked.reverse_go (cur : Link A) (acc : Link A) : IO (Link A) :=
    match cur {
        Link.nil => IO.pure acc,
        Link.node s => reverse_node s acc,
    }

#[terminating]
def reverse_node (s : Slot Full (Pair A (Link A))) (acc : Link A) : IO (Link A) := do {
    let p : Pair (Pair A (Link A)) (Slot Empty (Pair A (Link A))) <- Slot.take s;
    match p {
        Pair.pair payload empty => reverse_arm payload empty acc,
    }
}

def reverse_arm (payload : Pair A (Link A)) (empty : Slot Empty (Pair A (Link A))) (acc : Link A) : IO (Link A) :=
    match payload {
        Pair.pair x rest => reverse_relink x rest empty acc,
    }

/// The swap: `rest` becomes the cursor, and the handle just emptied is filled
/// with this node's element pointing at the accumulated list.
#[terminating]
def reverse_relink (x : A) (rest : Link A) (empty : Slot Empty (Pair A (Link A))) (acc : Link A) : IO (Link A) := do {
    let back : Slot Full (Pair A (Link A)) <- Slot.fill empty (Pair.pair x acc);
    Linked.reverse_go rest (Link.node back)
}

/// Swap the first two ELEMENTS in place. Both nodes keep their own handles and
/// only the pointers they hold are exchanged — the two-word relink a C linked
/// list would do with `next = next->next`.
///
/// A list with fewer than two nodes is returned unchanged (its handle is
/// refilled, not leaked).
pub def Linked.swap_adjacent (l : Link A) : IO (Link A) :=
    match l {
        Link.nil => IO.pure Link.nil,
        Link.node s1 => swap_first s1,
    }

def swap_first (s1 : Slot Full (Pair A (Link A))) : IO (Link A) := do {
    let p1 : Pair (Pair A (Link A)) (Slot Empty (Pair A (Link A))) <- Slot.take s1;
    match p1 {
        Pair.pair payload1 empty1 => swap_first_arm payload1 empty1,
    }
}

def swap_first_arm (payload1 : Pair A (Link A)) (empty1 : Slot Empty (Pair A (Link A))) : IO (Link A) :=
    match payload1 {
        Pair.pair a rest1 =>
            match rest1 {
                Link.nil => swap_single a empty1,
                Link.node s2 => swap_second a s2 empty1,
            },
    }

/// One node only: put the payload back in the handle it came from.
def swap_single (a : A) (empty1 : Slot Empty (Pair A (Link A))) : IO (Link A) := do {
    let back : Slot Full (Pair A (Link A)) <- Slot.fill empty1 (Pair.pair a Link.nil);
    IO.pure (Link.node back)
}

def swap_second (a : A) (s2 : Slot Full (Pair A (Link A))) (empty1 : Slot Empty (Pair A (Link A))) : IO (Link A) := do {
    let p2 : Pair (Pair A (Link A)) (Slot Empty (Pair A (Link A))) <- Slot.take s2;
    match p2 {
        Pair.pair payload2 empty2 => swap_second_arm a payload2 empty2 empty1,
    }
}

def swap_second_arm (a : A) (payload2 : Pair A (Link A)) (empty2 : Slot Empty (Pair A (Link A))) (empty1 : Slot Empty (Pair A (Link A))) : IO (Link A) :=
    match payload2 {
        Pair.pair b rest2 => swap_relink a b rest2 empty2 empty1,
    }

/// Both handles are refilled in swapped roles: the second node holds the first
/// element and the original tail, the first node holds the second element and
/// the second node.
def swap_relink (a : A) (b : A) (rest2 : Link A) (empty2 : Slot Empty (Pair A (Link A))) (empty1 : Slot Empty (Pair A (Link A))) : IO (Link A) := do {
    let n2 : Slot Full (Pair A (Link A)) <- Slot.fill empty2 (Pair.pair a rest2);
    let n1 : Slot Full (Pair A (Link A)) <- Slot.fill empty1 (Pair.pair b (Link.node n2));
    IO.pure (Link.node n1)
}
