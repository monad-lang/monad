/// A small, controlled JavaScript emitter.
///
/// The tree is deliberately narrow: expressions, statements and a module
/// header. Rendering is deterministic and escapes every string that comes
/// from data. `Js.Expr.raw` is the one trusted-literal escape hatch, and it
/// is named so a reviewer can find every use.
///
/// Identifiers are validated with `Js.valid_ident`; the renderer trusts the
/// caller to have done that (a generated `let` name is not user input). The
/// ABI-driven generator in `web_wasm` builds every name from its spec.

use std::list {List.intercalate}

pub type Js.Expr {
  raw (text : String),
  string (value : String),
  int (value : I64),
  bool (value : Bool),
  ident (name : String),
  member (base : Js.Expr) (field : String),
  call (f : Js.Expr) (args : List Js.Expr),
  arrow (params : List String) (body : List Js.Stmt),
  object (fields : List (Pair String Js.Expr)),
  array (items : List Js.Expr),
  null,
  undefined
}

pub type Js.Stmt {
  let_bind (name : String) (value : Js.Expr),
  assign (name : String) (value : Js.Expr),
  expr (value : Js.Expr),
  ret (value : Option Js.Expr),
  if_ (cond : Js.Expr) (then_ : List Js.Stmt) (else_ : List Js.Stmt),
  throw_ (value : Js.Expr)
}

pub struct Js.Module {
  header : List String,
  imports : List Js.Stmt,
  body : List Js.Stmt
}

// ── escaping and identifiers ────────────────────────────────────────────

/// A double-quoted JS string literal. `\`, `"`, newlines/tabs and `<` are
/// escaped; `<` becomes `<` so a generated `</script>` cannot close an
/// inline script tag. All other bytes (including multi-byte UTF-8) pass
/// through unchanged.
pub def Js.string_literal (s : String) : String :=
  String.concat_list ["\"", Js.escape_bytes (String.to_list s), "\""]

#[terminating]
def Js.escape_bytes (bytes : List U8) : String :=
  match bytes {
    List.empty => "",
    List.cons b rest =>
      String.concat (Js.escape_byte b) (Js.escape_bytes rest)
  }

def Js.escape_byte (b : U8) : String :=
  if U8.beq b 34u8 then "\\\""
  else if U8.beq b 92u8 then "\\\\"
  else if U8.beq b 10u8 then "\\n"
  else if U8.beq b 13u8 then "\\r"
  else if U8.beq b 9u8 then "\\t"
  else if U8.beq b 60u8 then "\\u003c"
  else String.from_list (List.singleton b)

/// ASCII identifier: `[A-Za-z_][A-Za-z0-9_]*`. JS permits `$` and Unicode
/// identifiers too; the generator does not need them, and rejecting them is
/// the safer default.
pub def Js.valid_ident (s : String) : Bool :=
  match String.to_list s {
    List.empty => false,
    List.cons first rest => Bool.and (Js.ident_start first) (Js.ident_rest_all rest)
  }

def Js.ident_start (b : U8) : Bool :=
  Bool.or (Js.is_alpha b) (U8.beq b 95u8)

def Js.ident_rest_byte (b : U8) : Bool :=
  Bool.or (Js.ident_start b) (Js.is_digit b)

#[terminating]
def Js.ident_rest_all (bytes : List U8) : Bool :=
  match bytes {
    List.empty => true,
    List.cons b rest => Bool.and (Js.ident_rest_byte b) (Js.ident_rest_all rest)
  }

def Js.is_alpha (b : U8) : Bool :=
  Bool.or
    (Bool.and (Bool.not (U8.lt b 65u8)) (Bool.not (U8.lt 90u8 b)))
    (Bool.and (Bool.not (U8.lt b 97u8)) (Bool.not (U8.lt 122u8 b)))

def Js.is_digit (b : U8) : Bool :=
  Bool.and (Bool.not (U8.lt b 48u8)) (Bool.not (U8.lt 57u8 b))

// ── rendering ───────────────────────────────────────────────────────────

#[terminating]
pub def Js.render_expr (e : Js.Expr) : String :=
  match e {
    Js.Expr.raw text => text,
    Js.Expr.string value => Js.string_literal value,
    Js.Expr.int value => I64.to_string value,
    Js.Expr.bool value => if value then "true" else "false",
    Js.Expr.ident name => name,
    Js.Expr.member base field => String.concat_list [Js.render_expr base, ".", field],
    Js.Expr.call f args =>
      String.concat_list [Js.render_expr f, "(", Js.render_exprs args, ")"],
    Js.Expr.arrow params body =>
      String.concat_list [
        "(", List.intercalate ", " params, ") => {\n",
        Js.render_stmts 1 body,
        "}"
      ],
    Js.Expr.object fields =>
      String.concat_list ["{", Js.render_fields fields, "}"],
    Js.Expr.array items =>
      String.concat_list ["[", Js.render_exprs items, "]"],
    Js.Expr.null => "null",
    Js.Expr.undefined => "undefined"
  }

#[terminating]
def Js.render_exprs (items : List Js.Expr) : String :=
  match items {
    List.empty => "",
    List.cons head rest =>
      match rest {
        List.empty => Js.render_expr head,
        List.cons _ _ => String.concat_list [Js.render_expr head, ", ", Js.render_exprs rest]
      }
  }

#[terminating]
def Js.render_fields (fields : List (Pair String Js.Expr)) : String :=
  match fields {
    List.empty => "",
    List.cons head rest =>
      match head {
        Pair.pair key value =>
          match rest {
            List.empty => String.concat_list [Js.string_literal key, ": ", Js.render_expr value],
            List.cons _ _ =>
              String.concat_list [
                Js.string_literal key, ": ", Js.render_expr value, ", ",
                Js.render_fields rest
              ]
          }
      }
  }

#[terminating]
pub def Js.render_stmt (indent : I64) (s : Js.Stmt) : String :=
  match s {
    Js.Stmt.let_bind name value =>
      String.concat_list ["let ", name, " = ", Js.render_expr value, ";\n"],
    Js.Stmt.assign name value =>
      String.concat_list [name, " = ", Js.render_expr value, ";\n"],
    Js.Stmt.expr value =>
      String.concat_list [Js.render_expr value, ";\n"],
    Js.Stmt.ret opt =>
      match opt {
        Option.none => "return;\n",
        Option.some value => String.concat_list ["return ", Js.render_expr value, ";\n"]
      },
    Js.Stmt.if_ cond then_ else_ =>
      String.concat_list [
        "if (", Js.render_expr cond, ") {\n",
        Js.render_stmts (I64.add indent 1) then_,
        Js.spaces indent, "}", Js.render_else indent else_, "\n"
      ],
    Js.Stmt.throw_ value =>
      String.concat_list ["throw ", Js.render_expr value, ";\n"]
  }

#[terminating]
def Js.render_else (indent : I64) (stmts : List Js.Stmt) : String :=
  if List.is_empty stmts
  then ""
  else
    String.concat_list [
      " else {\n",
      Js.render_stmts (I64.add indent 1) stmts,
      Js.spaces indent, "}"
    ]

#[terminating]
pub def Js.render_stmts (indent : I64) (stmts : List Js.Stmt) : String :=
  match stmts {
    List.empty => "",
    List.cons head rest =>
      String.concat_list [
        Js.spaces indent, Js.render_stmt indent head, Js.render_stmts indent rest
      ]
  }

#[terminating]
def Js.spaces (n : I64) : String :=
  if I64.lt n 1 then "" else String.concat "  " (Js.spaces (I64.sub n 1))

#[terminating]
def Js.render_header (lines : List String) : String :=
  match lines {
    List.empty => "",
    List.cons line rest =>
      String.concat_list ["// ", line, "\n", Js.render_header rest]
  }

/// The module text: header comments, then imports, a blank line, then body.
pub def Js.render_module (m : Js.Module) : String :=
  String.concat_list [
    Js.render_header m.header,
    Js.render_stmts 0 m.imports,
    "\n",
    Js.render_stmts 0 m.body
  ]
