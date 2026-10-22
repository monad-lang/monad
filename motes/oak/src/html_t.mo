// The indexed page-assembly transformer: `HtmlT M I J A` is a hand-rolled
// ReaderT over `Render M` on top of a StateT over `Page`, i.e.
// `Render M -> Page -> M (Pair Page A)`.
//
// The shape follows tui's `TuiT` (motes/tui/src/tuit.mo) and shuttle's
// `Agent`, with the state-threading difference that TuiT does not need:
// `bind`, `map` and `and_then` must carry the `Page` returned by the first
// computation. The `*_step` helpers exist so every class call in an
// instance body stays a DIRECT `Monad.bind`/`Monad.pure` reference, while
// the matches live in helpers that contain no class call at all.
//
// Lifecycle indices: Open (head/body writable) -> Sealed (frozen) ->
// Emitted (document written; only `lift` accepts it).

use init::transformers {ResultT, ResultT.lift}
use std::io {IO.flush_stdout, IO.write_stdout}
use lib::elements {Html.document}
use xml_html::html {Html.Node, Html.to_string}
use xml_html::html {}

// ═══ Types ═══
//
// `Render` and `HtmlT` are single-constructor `type`s: parameterized
// structs do not parse. The lifecycle markers are phantom TYPES, not an
// enum (an enum index is a kind error). None of these go inside a `with`
// block; only defs do.

/// The write capability: how an emitted document leaves the transformer.
pub type Render (M : Type -> Type) {
    render (write : String -> M Unit)
}

/// Page state: head and body children in source order. Non-parameterized,
/// so it is a real `struct` (field access and update syntax).
pub struct Page {
    head : List Html.Node,
    body : List Html.Node
}

pub type Open {}
pub type Sealed {}
pub type Emitted {}

/// One page-assembly step from phase `I` to phase `J` producing `A`.
pub type HtmlT (M : Type -> Type) (I : Type) (J : Type) (A : Type) {
    html_t (run : Render M -> Page -> M (Pair Page A))
}

// ═══ Render: accessors and the landed stacks ═══

def io_write_flush (s : String) : IO Unit := do {
    IO.write_stdout s;
    IO.flush_stdout;
    return Unit.unit
}

with Render {
    pub def write {M : Type -> Type} (r : Render M) (s : String) : M Unit :=
        match r { Render.render w => w s }

    /// The production sink: write and flush stdout, the `Term.io` contract.
    pub def io : Render IO :=
        Render.render io_write_flush

    /// Wrap the production sink in `PageM`, Oak's `ResultT` stack.
    pub def lift_page (r : Render IO) : Render PageM :=
        Render.render (fn (s : String) => PageM.page_m (ResultT.lift (Render.write r s)))
}

// ═══ PageM: the production ResultT stack ═══
//
// `ResultT String IO` behind a simple-headed newtype. The wrapper is
// load-bearing, not cosmetic: passing `Monad (ResultT String IO)` as a
// dictionary through the polymorphic HtmlT ops fails to synthesize (the
// same dictionary gap shuttle's mock records -- see
// motes/shuttle/src/wire/mock.mo's `Mock.send`), while a concrete
// `Monad PageM` instance dispatches reliably.

pub type PageM A {
    page_m (underlying : ResultT String IO A)
}

pub def PageM.run {A : Type} (m : PageM A) : ResultT String IO A :=
    match m { PageM.page_m r => r }

pub def PageM.pure {A : Type} (a : A) : PageM A :=
    PageM.page_m (ResultT.mk (IO.pure (Result.ok a)))

def page_bind_step {A : Type} {B : Type}
    (f : A -> PageM B) (r : Result String A) : IO (Result String B) :=
    match r {
        Result.ok a => ResultT.run (PageM.run (f a)),
        Result.err e => IO.pure (Result.err e)
    }

def page_bind_run {A : Type} {B : Type}
    (ma : PageM A) (f : A -> PageM B) : IO (Result String B) :=
    Monad.bind (ResultT.run (PageM.run ma)) (page_bind_step f)

pub instance Monad PageM {
    def pure (a : A) : PageM A := PageM.pure a
    def bind (ma : PageM A) (f : A -> PageM B) : PageM B :=
        PageM.page_m (ResultT.mk (page_bind_run ma f))
}

// ═══ Page: the page state helpers ═══
//
// Every literal/update is bound by an annotated let and then returned:
// a bare struct literal in argument/return position can compile to
// garbage self-hosted.

with Page {
    pub def empty : Page :=
        let d : Page := { head := List.empty, body := List.empty } in d

    pub def append_head (d : Page) (n : Html.Node) : Page :=
        let d2 : Page := { d with head := List.append d.head (List.cons n List.empty) } in d2

    pub def append_heads (d : Page) (ns : List Html.Node) : Page :=
        let d2 : Page := { d with head := List.append d.head ns } in d2

    pub def append_body (d : Page) (n : Html.Node) : Page :=
        let d2 : Page := { d with body := List.append d.body (List.cons n List.empty) } in d2

    pub def append_bodies (d : Page) (ns : List Html.Node) : Page :=
        let d2 : Page := { d with body := List.append d.body ns } in d2
}

// ═══ Page-threading helpers ═══
//
// No class call in any of these, so they take no `[Monad M]` dictionary.
// `bind_step`/`and_then_step` match the returned state and run the next
// step against it; `map_step` is pure.

def emit_document (d : Page) : String :=
    Html.to_string (Html.document d.head d.body)

def bind_step {M : Type -> Type} {J : Type} {K : Type} {A : Type} {B : Type}
    (f : A -> HtmlT M J K B) (r : Render M) (p : Pair Page A) : M (Pair Page B) :=
    match p { Pair.pair d a => HtmlT.run (f a) r d }

def and_then_step {M : Type -> Type} {J : Type} {K : Type} {A : Type} {B : Type}
    (second : HtmlT M J K B) (r : Render M) (p : Pair Page A) : M (Pair Page B) :=
    match p { Pair.pair d _ => HtmlT.run second r d }

def map_step {A : Type} {B : Type} (f : A -> B) (p : Pair Page A) : Pair Page B :=
    match p { Pair.pair d a => Pair.pair d (f a) }

// ═══ HtmlT: accessors, structure and lifecycle ops ═══

with HtmlT {
    pub def run {M : Type -> Type} {I : Type} {J : Type} {A : Type}
        (ma : HtmlT M I J A) (r : Render M) (d : Page) : M (Pair Page A) :=
        match ma { HtmlT.html_t action => action r d }

    pub def pure [Monad M] {I : Type} {A : Type} (a : A) : HtmlT M I I A :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) => Monad.pure (Pair.pair d a))

    pub def bind [Monad M] {I : Type} {J : Type} {K : Type} {A : Type} {B : Type}
        (ma : HtmlT M I J A) (f : A -> HtmlT M J K B) : HtmlT M I K B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run ma r d) (bind_step f r))

    pub def map [Monad M] {I : Type} {J : Type} {A : Type} {B : Type}
        (f : A -> B) (ma : HtmlT M I J A) : HtmlT M I J B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run ma r d)
                (fn (p : Pair Page A) => Monad.pure (map_step f p)))

    pub def and_then [Monad M] {I : Type} {J : Type} {K : Type} {A : Type} {B : Type}
        (first : HtmlT M I J A) (second : HtmlT M J K B) : HtmlT M I K B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run first r d) (and_then_step second r))

    /// Run a base-monad action without touching the page.
    pub def lift [Monad M] {I : Type} {A : Type} (m : M A) : HtmlT M I I A :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.bind m (fn (a : A) => Monad.pure (Pair.pair d a)))

    pub def head_node [Monad M] (n : Html.Node) : HtmlT M Open Open Unit :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.pure (Pair.pair (Page.append_head d n) Unit.unit))

    pub def head_nodes [Monad M] (ns : List Html.Node) : HtmlT M Open Open Unit :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.pure (Pair.pair (Page.append_heads d ns) Unit.unit))

    pub def body_node [Monad M] (n : Html.Node) : HtmlT M Open Open Unit :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.pure (Pair.pair (Page.append_body d n) Unit.unit))

    pub def body_nodes [Monad M] (ns : List Html.Node) : HtmlT M Open Open Unit :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.pure (Pair.pair (Page.append_bodies d ns) Unit.unit))

    /// Freeze the draft. A pure index transition; the state is unchanged.
    pub def seal [Monad M] : HtmlT M Open Sealed Unit :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) =>
            Monad.pure (Pair.pair d Unit.unit))

    /// Serialize the document once and hand it to the sink.
    pub def emit [Monad M] : HtmlT M Sealed Emitted Unit :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (Render.write r (emit_document d))
                (fn (_ : Unit) => Monad.pure (Pair.pair d Unit.unit)))
}

// ═══ Instances ═══
//
// All five IndexedMonad methods are spelled out: a default that is only
// inherited passes checking and fails at runtime. The equal-index Monad
// instance is hand-written because the prelude's generic bridge has a
// variable head and never dispatches.

pub instance [Monad M] IndexedMonad (HtmlT M) {
    def pure (a : A) : HtmlT M I I A :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) => Monad.pure (Pair.pair d a))

    def bind (ma : HtmlT M I J A) (f : A -> HtmlT M J K B) : HtmlT M I K B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run ma r d) (bind_step f r))

    def map (f : A -> B) (ma : HtmlT M I J A) : HtmlT M I J B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run ma r d)
                (fn (p : Pair Page A) => Monad.pure (map_step f p)))

    def and_then (first : HtmlT M I J A) (second : HtmlT M J K B) : HtmlT M I K B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run first r d) (and_then_step second r))

    def lift (a : A) : HtmlT M I I A :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) => Monad.pure (Pair.pair d a))
}

pub instance [Monad M] Monad (HtmlT M I I) {
    def pure (a : A) : HtmlT M I I A :=
        HtmlT.html_t (fn (_ : Render M) (d : Page) => Monad.pure (Pair.pair d a))

    def bind (ma : HtmlT M I I A) (f : A -> HtmlT M I I B) : HtmlT M I I B :=
        HtmlT.html_t (fn (r : Render M) (d : Page) =>
            Monad.bind (HtmlT.run ma r d) (bind_step f r))
}
