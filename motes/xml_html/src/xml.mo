/// XML markup nodes and their serializer.
///
/// Independent of `html.mo` on purpose: separate constructors, escapers
/// and `BEq`, the same policy `lang/toml.mo` follows relative to
/// `lang/json.mo`. The two formats only meet in `lib.mo`'s re-exports and
/// in sharing the `parsec` substrate.
///
/// The parser (a later phase) produces these nodes: nested elements with
/// attributes, text and comments. Namespaces are opaque attribute names;
/// CDATA, DTDs and processing instructions are parse errors.

use init::string {}
use parsec::core {is_empty}
use parsec::combinators {utf8_char_width}

// Dotted type declarations, not `with Xml { type ... }`: constructors of a
// `with`-declared type are not visible across modules on the Rust host,
// while `Xml.Node.node_text` on a dotted declaration is. (See html.mo.)
pub type Xml.Attr {
    attr (name : String) (value : String)
}

pub type Xml.Node {
    node_element (tag : String) (attrs : List Xml.Attr) (children : List Xml.Node),
    node_text (content : String),
    node_comment (content : String)
}

with Xml {
    pub def to_string (n : Xml.Node) : String := xml_node_to_string n

    pub def beq (a b : Xml.Node) : Bool := xml_node_beq a b
}

// ─── Escaping ───

def xml_escape_text_char (c : String) : String :=
    if String.beq "&" c then "&amp;"
    else if String.beq "<" c then "&lt;"
    else if String.beq ">" c then "&gt;"
    else c

def xml_escape_attr_char (c : String) : String :=
    if String.beq "&" c then "&amp;"
    else if String.beq "<" c then "&lt;"
    else if String.beq ">" c then "&gt;"
    else if String.beq "\"" c then "&quot;"
    else c

#[terminating]
def xml_escape_pieces (escape_one : String -> String) (input : String) (acc : List String) : List String :=
    if is_empty input
    then List.reverse acc
    else
        let width : I64 := utf8_char_width input in
        let step : I64 := if width < 1 then 1 else width in
        let ch : String := String.slice input 0 step in
        xml_escape_pieces escape_one (String.drop step input) (List.cons (escape_one ch) acc)

def xml_escape_text (input : String) : String :=
    String.concat_list (xml_escape_pieces xml_escape_text_char input List.empty)

def xml_escape_attr (input : String) : String :=
    String.concat_list (xml_escape_pieces xml_escape_attr_char input List.empty)

// ─── Serializer ───

def xml_attr_to_string (a : Xml.Attr) : String :=
    match a {
        attr name value =>
            String.concat " " (String.concat name (String.concat "=\"" (String.concat (xml_escape_attr value) "\"")))
    }

def xml_attrs_to_string (attrs : List Xml.Attr) : String :=
    match attrs {
        empty => "",
        cons a rest => String.concat (xml_attr_to_string a) (xml_attrs_to_string rest)
    }

def xml_children_to_string (children : List Xml.Node) : String :=
    match children {
        empty => "",
        cons child rest => String.concat (xml_node_to_string child) (xml_children_to_string rest)
    }

def xml_open_tag (tag : String) (attrs : List Xml.Attr) : String :=
    String.concat "<" (String.concat tag (String.concat (xml_attrs_to_string attrs) ">"))

def xml_close_tag (tag : String) : String :=
    String.concat "</" (String.concat tag ">")

def xml_node_to_string (n : Xml.Node) : String :=
    match n {
        node_element tag attrs children =>
            String.concat (xml_open_tag tag attrs)
                (String.concat (xml_children_to_string children) (xml_close_tag tag)),
        node_text content => xml_escape_text content,
        node_comment content => String.concat "<!--" (String.concat content "-->")
    }

// ─── Equality ───

def xml_attr_beq (a b : Xml.Attr) : Bool :=
    match a {
        attr n1 v1 => match b {
            attr n2 v2 => String.beq n1 n2 && String.beq v1 v2
        }
    }

def xml_attrs_beq (a b : List Xml.Attr) : Bool :=
    match a {
        empty => match b { empty => true, cons _ _ => false },
        cons x xs => match b {
            empty => false,
            cons y ys => xml_attr_beq x y && xml_attrs_beq xs ys
        }
    }

def xml_children_beq (a b : List Xml.Node) : Bool :=
    match a {
        empty => match b { empty => true, cons _ _ => false },
        cons x xs => match b {
            empty => false,
            cons y ys => xml_node_beq x y && xml_children_beq xs ys
        }
    }

def xml_node_beq (a b : Xml.Node) : Bool :=
    match a {
        node_element t1 a1 c1 => match b {
            node_element t2 a2 c2 =>
                String.beq t1 t2 && xml_attrs_beq a1 a2 && xml_children_beq c1 c2,
            _ => false
        },
        node_text c1 => match b {
            node_text c2 => String.beq c1 c2,
            _ => false
        },
        node_comment c1 => match b {
            node_comment c2 => String.beq c1 c2,
            _ => false
        }
    }

pub instance BEq Xml.Attr {
    def beq (a b : Xml.Attr) : Bool := xml_attr_beq a b
}

pub instance BEq Xml.Node {
    def beq (a b : Xml.Node) : Bool := xml_node_beq a b
}
