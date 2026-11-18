// Stories: feedback and data display.

use oak::typed {Oak.Node}
use oak::elements {Html.text}
use std::list {List.intercalate}
use oak::events {Html.on_click}
use oak_ui::vocab {
    Ui.Opt, Ui.Tone, Ui.primary, Ui.success, Ui.warning, Ui.danger, Ui.info, Ui.neutral, Ui.solid, Ui.outline,
    Ui.small, Ui.large, Ui.gap, Ui.cols,
}
use oak_ui::layout {Ui.stack, Ui.cluster, Ui.grid}
use oak_ui::typography {Ui.text}
use oak_ui::button {Ui.button}
use oak_ui::feedback {
    Ui.Toast, Ui.alert, Ui.badge, Ui.tag, Ui.spinner, Ui.progress, Ui.skeleton, Ui.empty_state, Ui.toast,
    Ui.toast_region,
}
use oak_ui::data {
    Ui.Column, Ui.SortState, Ui.column, Ui.Column.sortable, Ui.Column.numeric, Ui.striped, Ui.hoverable,
    Ui.card, Ui.description_list, Ui.list_group, Ui.avatar, Ui.stat, Ui.table,
}
use oak_ui::graph_layout {Ui.GraphSpec, Ui.GraphNode, Ui.GraphEdge, Ui.GraphGroup, Ui.graph_layout}
use oak_ui::graph {Ui.GraphMsg, Ui.GraphView, Ui.GraphView.initial, Ui.GraphView.update, Ui.graph}
use lib::story {
    Book.Story, Book.Ctx, Book.Msg, Book.story, Book.text, Book.flag, Book.int, Book.choice, Book.knob_text,
    Book.knob_bool, Book.knob_int, Book.tone_opt, Book.size_opt, Book.tone_knob, Book.size_knob, Book.action,
    Book.set, Book.set_and_log, Book.state, Book.state_bool, Book.state_int, Book.parse_int,
}

def alert_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    if Book.state_bool ctx "dismissed"
    then Ui.button [Ui.small] [Html.on_click (Book.set_and_log "dismissed" "false" "restore")] [Html.text "Show the alert again"]
    else
        Ui.alert [Book.tone_opt ctx] (Book.knob_text ctx "title")
            (if Book.knob_bool ctx "dismissable" then Option.some (Book.set_and_log "dismissed" "true" "dismiss") else Option.none)
            List.empty [Html.text (Book.knob_text ctx "body")]

def badges_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Ui.cluster List.empty List.empty
            [Ui.badge [Ui.neutral] "Draft", Ui.badge [Ui.primary] "New", Ui.badge [Ui.success] "Active",
                Ui.badge [Ui.warning] "Pending", Ui.badge [Ui.danger] "Failed", Ui.badge [Ui.info] "Info"],
            Ui.cluster List.empty List.empty
                [Ui.badge [Ui.primary, Ui.solid] "Solid", Ui.badge [Ui.primary, Ui.outline] "Outline",
                    Ui.badge [Book.tone_opt ctx, Book.size_opt ctx] (Book.knob_text ctx "label")],
            Ui.cluster List.empty List.empty (tags ctx)]

def tags (ctx : Book.Ctx) : List (Oak.Node Book.Msg) :=
    List.append
        (if Book.state_bool ctx "rust-removed" then List.empty
            else [Ui.tag [Ui.primary] "rust" (Option.some (Book.set_and_log "rust-removed" "true" "remove tag"))])
        [Ui.tag List.empty "monad" (Option.some (Book.action "remove tag" "monad")), Ui.tag [Ui.success] "static" Option.none]

def progress_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 4] List.empty
        [Ui.progress [Book.tone_opt ctx, Book.size_opt ctx] "Upload" (Book.knob_int ctx "value") 100,
            Ui.progress [Ui.info] "Working" 0 0,
            Ui.cluster List.empty List.empty
                [Ui.spinner [Ui.small] "Loading", Ui.spinner [Ui.primary] "Loading", Ui.spinner [Ui.large, Ui.success] "Loading"],
            Ui.skeleton List.empty (Book.knob_int ctx "skeleton lines")]

def empty_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.empty_state List.empty (Book.knob_text ctx "title") (Book.knob_text ctx "description")
        [Ui.button [Ui.primary] [Html.on_click (Book.action "create" "")] [Html.text "Create project"]]

def toast_list (ctx : Book.Ctx) : List Ui.Toast :=
    List.append
        (if Book.state_bool ctx "t1-gone" then List.empty else [Ui.toast "t1" Ui.Tone.tone_success "Saved" "Your changes are live."])
        (if Book.state_bool ctx "t2-gone" then List.empty else [Ui.toast "t2" Ui.Tone.tone_danger "Upload failed" "The file is larger than 10 MB."])

def dismiss_toast (id : String) : Book.Msg := Book.set_and_log (String.concat id "-gone") "true" "dismiss toast"

def toasts_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.stack [Ui.gap 3] List.empty
        [Ui.button [Ui.small] [Html.on_click Book.Msg.book_reset] [Html.text "Bring the toasts back"],
            Ui.toast_region List.empty (toast_list ctx) dismiss_toast]

struct BookFruit {
    id : String,
    name : String,
    origin : String,
    stock : I64
}

def fruit (id : String) (name : String) (origin : String) (stock : I64) : BookFruit :=
    { id := id, name := name, origin := origin, stock := stock }

def fruits : List BookFruit :=
    [fruit "1" "Apple" "Norway" 120, fruit "2" "Banana" "Ecuador" 40, fruit "3" "Cherry" "Turkey" 300,
        fruit "4" "Date" "Egypt" 15]

def fruit_name (f : BookFruit) : Oak.Node Book.Msg := Html.text f.name
def fruit_origin (f : BookFruit) : Oak.Node Book.Msg := Html.text f.origin
def fruit_stock (f : BookFruit) : Oak.Node Book.Msg :=
    if I64.lt f.stock 20 then Ui.badge [Ui.danger] (I64.to_string f.stock) else Html.text (I64.to_string f.stock)
def fruit_id (f : BookFruit) : String := f.id

def fruit_less (key : String) (a : BookFruit) (b : BookFruit) : Bool :=
    if String.beq key "stock" then I64.lt a.stock b.stock
    else if String.beq key "origin" then String.lt a.origin b.origin
    else String.lt a.name b.name

#[terminating]
def insert_sorted (key : String) (asc : Bool) (x : BookFruit) (xs : List BookFruit) : List BookFruit :=
    match xs {
        List.empty => [x],
        List.cons y rest =>
            let before : Bool := if asc then fruit_less key x y else fruit_less key y x in
            if before then List.cons x xs else List.cons y (insert_sorted key asc x rest),
    }

#[terminating]
def sort_fruits (key : String) (asc : Bool) (xs : List BookFruit) : List BookFruit :=
    match xs {
        List.empty => List.empty,
        List.cons x rest => insert_sorted key asc x (sort_fruits key asc rest),
    }

def sort_state (ctx : Book.Ctx) : Ui.SortState :=
    { column := Book.state ctx "sort" "", ascending := Bool.not (String.beq (Book.state ctx "dir" "asc") "desc") }

def sort_msg (ctx : Book.Ctx) : String -> Book.Msg :=
    let current : Ui.SortState := sort_state ctx in
    fn (key : String) =>
        if String.beq current.column key
        then Book.set_and_log "dir" (if current.ascending then "desc" else "asc") (String.concat "sort " key)
        else Book.set_and_log "sort" key "sort"

def table_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let s : Ui.SortState := sort_state ctx in
    let rows : List BookFruit := if String.is_empty s.column then fruits else sort_fruits s.column s.ascending fruits in
    let cols : List (Ui.Column BookFruit Book.Msg) :=
        [Ui.Column.sortable (Ui.column "name" "Fruit" fruit_name),
            Ui.Column.sortable (Ui.column "origin" "Origin" fruit_origin),
            Ui.Column.numeric (Ui.Column.sortable (Ui.column "stock" "Stock" fruit_stock))] in
    let opts : List Ui.Opt :=
        List.append (if Book.knob_bool ctx "striped" then [Ui.striped] else List.empty)
            (List.append (if Book.knob_bool ctx "hover" then [Ui.hoverable] else List.empty)
                (if Book.knob_bool ctx "dense" then [Ui.small] else List.empty)) in
    Ui.table opts "Fruit stock" cols rows fruit_id s (sort_msg ctx) List.empty

def data_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    Ui.grid [Ui.cols 2, Ui.gap 4] List.empty
        [Ui.card List.empty [Html.text "Profile"]
            [Ui.stack [Ui.gap 3] List.empty
                [Ui.cluster List.empty List.empty
                    [Ui.avatar List.empty (Book.knob_text ctx "name") "", Ui.avatar [Ui.primary] "Grace Hopper" "",
                        Ui.avatar [Ui.small, Ui.success] "Linus" ""],
                    Ui.description_list List.empty
                        [Pair.pair "Name" (Html.text (Book.knob_text ctx "name")), Pair.pair "Role" (Html.text "Engineer"),
                            Pair.pair "Status" (Ui.badge [Ui.success] "Active")]]]
            [Ui.button [Ui.small] [Html.on_click (Book.action "edit profile" "")] [Html.text "Edit"]],
            Ui.card List.empty [Html.text "This month"]
                [Ui.grid [Ui.cols 2, Ui.gap 4] List.empty
                    [Ui.stat List.empty "Revenue" "$48.2k" "+12%", Ui.stat List.empty "Churn" "2.1%" "-0.4%",
                        Ui.stat List.empty "Users" "1,204" ""]] List.empty,
            Ui.list_group List.empty [Html.text "Inbox", Html.text "Archive", Html.text "Spam"]]

// ─── Graph ───

def gnode (id : String) (group : String) : Ui.GraphNode :=
    { id := id, label := id, group := group, cls := "", tip := String.concat_list [group, "::", id] }

def gedge (a : String) (b : String) (w : I64) : Ui.GraphEdge := { from := a, to := b, weight := w, cls := "" }

def ggroup (id : String) (parent : String) : Ui.GraphGroup := { id := id, label := id, parent := parent, cls := "" }

/// A small checker-shaped call graph: two modules inside one mote, and a
/// helper module outside it, with one recursive cycle.
def graph_spec (grouped : Bool) : Ui.GraphSpec :=
    let g : String -> String := fn (m : String) => if grouped then m else "" in
    { nodes := [gnode "check_decl" (g "infer"), gnode "infer" (g "infer"), gnode "check" (g "infer"),
        gnode "unify" (g "unify"), gnode "whnf" (g "unify"), gnode "occurs" (g "unify"),
        gnode "subst" (g "subst"), gnode "shift" (g "subst")],
        edges := [gedge "check_decl" "check" 3, gedge "check" "infer" 5, gedge "infer" "check" 2,
            gedge "infer" "unify" 8, gedge "check" "unify" 1, gedge "unify" "whnf" 4, gedge "unify" "occurs" 1,
            gedge "whnf" "subst" 2, gedge "subst" "shift" 6, gedge "infer" "whnf" 1],
        groups := if grouped
            then [ggroup "lang" "", ggroup "infer" "lang", ggroup "unify" "lang", ggroup "subst" ""]
            else List.empty }

/// The pan/zoom/drag half of the view, kept in one story-state key
/// (`pan_x,pan_y,zoom,dragging,drag_x,drag_y`): a book message sets one key,
/// and a drag changes several fields at once.
#[terminating]
def nth_int (parts : List String) (i : I64) (default : I64) : I64 :=
    match parts {
        List.empty => default,
        List.cons p rest => if i <= 0 then Book.parse_int p else nth_int rest (i - 1) default,
    }

def graph_view_of (ctx : Book.Ctx) : Ui.GraphView :=
    let parts : List String := String.split (Book.state ctx "view" "0,0,100,0,0,0") "," in
    { Ui.GraphView.initial with
        pan_x := nth_int parts 0 0, pan_y := nth_int parts 1 0, zoom := nth_int parts 2 100,
        dragging := nth_int parts 3 0 == 1, drag_x := nth_int parts 4 0, drag_y := nth_int parts 5 0,
        selected := Book.state ctx "selected" "" }

def encode_view (v : Ui.GraphView) : String :=
    List.intercalate "," (List.map I64.to_string
        [v.pan_x, v.pan_y, v.zoom, if v.dragging then 1 else 0, v.drag_x, v.drag_y])

def graph_msg (ctx : Book.Ctx) (m : Ui.GraphMsg) : Book.Msg :=
    let v : Ui.GraphView := Ui.GraphView.update (graph_view_of ctx) m in
    match m {
        Ui.GraphMsg.graph_select _ => Book.set_and_log "selected" v.selected "select",
        _ => Book.set "view" (encode_view v),
    }

def graph_story (ctx : Book.Ctx) : Oak.Node Book.Msg :=
    let spec : Ui.GraphSpec := graph_spec (Book.knob_bool ctx "groups") in
    let base : Ui.GraphView := graph_view_of ctx in
    let marks : List String := if Book.knob_bool ctx "highlight unify" then ["unify"] else List.empty in
    let v : Ui.GraphView := { base with highlighted := marks } in
    Ui.graph List.empty "Type checker calls" (Ui.graph_layout spec) v (graph_msg ctx) List.empty

pub def display_stories : List Book.Story :=
    [Book.story "alert" "Feedback" "Alert" "Danger and warning use role=alert; the rest role=status."
        [Book.text "title" "Heads up", Book.text "body" "Your trial ends in 3 days.", Book.tone_knob, Book.flag "dismissable" true]
        alert_story,
        Book.story "badges-tags" "Feedback" "Badges and tags" "Status labels and removable chips."
            [Book.text "label" "Custom", Book.tone_knob, Book.size_knob] badges_story,
        Book.story "progress" "Feedback" "Progress and loading" "Progress bars, spinners and skeletons."
            [Book.int "value" 60, Book.tone_knob, Book.size_knob, Book.int "skeleton lines" 3] progress_story,
        Book.story "empty-state" "Feedback" "Empty state" "What an empty list shows."
            [Book.text "title" "No projects yet", Book.text "description" "Projects you create will show up here."] empty_story,
        Book.story "toasts" "Feedback" "Toasts" "A controlled, keyed notification region (shown inside the frame here)." List.empty toasts_story,
        Book.story "table" "Data" "Table" "Click a header to sort; the story owns the sort state."
            [Book.flag "striped" true, Book.flag "hover" true, Book.flag "dense" false] table_story,
        Book.story "data-display" "Data" "Cards, stats and lists" "Cards, avatars, description lists, stats and list groups."
            [Book.text "name" "Ada Lovelace"] data_story,
        Book.story "graph" "Data" "Graph"
            "A layered call graph with nested groups. Click a node to select it; the wheel and toolbar zoom."
            [Book.flag "groups" true, Book.flag "highlight unify" true] graph_story]
