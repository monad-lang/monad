/// Goldens and behaviour for data display.

use web_event::event {WebEvent}
use oak::typed {Oak.Node}
use oak::elements {Html.text}
use lib::tests::support {ui_renders, ui_has, ui_first_msg}
use lib::vocab {Ui.small}
use lib::data {
    Ui.Column, Ui.SortState, Ui.SortState.none, Ui.SortState.toggle, Ui.column, Ui.Column.sortable,
    Ui.Column.numeric, Ui.striped, Ui.card, Ui.description_list, Ui.list_group, Ui.avatar, Ui.stat,
    Ui.table,
}

struct DataTestRow {
    id : String,
    name : String,
    qty : I64
}

type DataTestMsg { sort_by (key : String) }

def name_cell (r : DataTestRow) : Oak.Node DataTestMsg := Html.text r.name

def qty_cell (r : DataTestRow) : Oak.Node DataTestMsg := Html.text (I64.to_string r.qty)

def row_id (r : DataTestRow) : String := r.id

def test_columns : List (Ui.Column DataTestRow DataTestMsg) :=
    [Ui.Column.sortable (Ui.column "name" "Name" name_cell),
        Ui.Column.numeric (Ui.column "qty" "Qty" qty_cell)]

def apple : DataTestRow := { id := "a", name := "Apple", qty := 3 }

def pear : DataTestRow := { id := "b", name := "Pear", qty := 10 }

def test_rows : List DataTestRow := [apple, pear]

def sorted_name : Ui.SortState := { column := "name", ascending := false }

def test_table : Oak.Node DataTestMsg :=
    Ui.table [Ui.striped] "Fruit" test_columns test_rows row_id sorted_name DataTestMsg.sort_by List.empty

#[test]
def test_table_structure : Bool :=
    ui_renders test_table
        (String.concat_list [
            "<div class=\"oak-table-wrap\"><table class=\"oak-table oak-table--striped\">",
            "<caption class=\"oak-table__caption\">Fruit</caption>",
            "<thead><tr><th class=\"oak-table__th\" scope=\"col\" aria-sort=\"descending\">",
            "<button class=\"oak-table__sort\" type=\"button\">Name<span class=\"oak-icon\" aria-hidden=\"true\">\u{2193}</span></button></th>",
            "<th class=\"oak-table__th oak-table__cell--end\" scope=\"col\">Qty</th></tr></thead>",
            "<tbody><tr data-oak-key=\"a\" class=\"oak-table__row\"><td class=\"oak-table__td\">Apple</td><td class=\"oak-table__td oak-table__cell--end\">3</td></tr>",
            "<tr data-oak-key=\"b\" class=\"oak-table__row\"><td class=\"oak-table__td\">Pear</td><td class=\"oak-table__td oak-table__cell--end\">10</td></tr></tbody>",
            "</table></div>"])

#[test]
def test_table_header_click_sorts : Bool :=
    let e : WebEvent := { kind := "click" } in
    match ui_first_msg test_table e {
        Option.some m => match m { DataTestMsg.sort_by k => String.beq k "name" },
        Option.none => false,
    }

#[test]
def test_sort_toggle : Bool :=
    let first : Ui.SortState := Ui.SortState.toggle Ui.SortState.none "name" in
    let second : Ui.SortState := Ui.SortState.toggle first "name" in
    let other : Ui.SortState := Ui.SortState.toggle second "qty" in
    first.ascending && String.beq first.column "name"
        && Bool.not second.ascending
        && other.ascending && String.beq other.column "qty"

#[test]
def test_table_dense : Bool :=
    let t : Oak.Node DataTestMsg :=
        Ui.table [Ui.small] "" test_columns List.empty row_id Ui.SortState.none DataTestMsg.sort_by List.empty in
    ui_has t "<table class=\"oak-table oak-table--sm\"><thead>"
        && ui_has t "aria-sort=\"none\""

#[test]
def test_card_slots : Bool :=
    ui_renders (Ui.card List.empty [Html.text "H"] [Html.text "B"] List.empty)
        "<section class=\"oak-card\"><header class=\"oak-card__header\">H</header><div class=\"oak-card__body\">B</div></section>"

#[test]
def test_description_list : Bool :=
    ui_renders (Ui.description_list List.empty [Pair.pair "Owner" (Html.text "Ada")])
        "<dl class=\"oak-dl\"><dt class=\"oak-dl__term\">Owner</dt><dd class=\"oak-dl__detail\">Ada</dd></dl>"

#[test]
def test_list_group : Bool :=
    ui_renders (Ui.list_group List.empty [Html.text "a", Html.text "b"])
        "<ul class=\"oak-list\"><li class=\"oak-list__item\">a</li><li class=\"oak-list__item\">b</li></ul>"

#[test]
def test_avatar_initials_and_image : Bool :=
    ui_renders (Ui.avatar List.empty "Ada Lovelace" "")
        "<span class=\"oak-avatar oak-tone-neutral\" role=\"img\" aria-label=\"Ada Lovelace\">AL</span>"
        && ui_renders (Ui.avatar [Ui.small] "Ada" "/a.png")
            "<img class=\"oak-avatar oak-avatar--sm\" src=\"/a.png\" alt=\"Ada\">"
        && ui_has (Ui.avatar List.empty "\u{00C5}se" "") ">\u{00C5}</span>"
        && ui_has (Ui.avatar List.empty "Ada  Lovelace" "") ">AL</span>"

#[test]
def test_stat_delta_tone : Bool :=
    ui_renders (Ui.stat List.empty "Revenue" "$12k" "+4%")
        "<div class=\"oak-stat\"><div class=\"oak-stat__label\">Revenue</div><div class=\"oak-stat__value\">$12k</div><div class=\"oak-stat__delta oak-tone-success\">+4%</div></div>"
