use super::*;

/// Mirrors the self-hosted `with`-block battery (`test_with_block_*` in
/// `lang/src/parser.mo`): every inner decl's name gains the block's
/// dotted prefix, inner decls splice flat, and `with` is a
/// word-boundary keyword.
#[test]
fn test_with_block_prefixes_def_name() {
  let s = r#"with Ns { def a : I64 := 1 }"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Generated(inner) => {
      assert_eq!(inner.len(), 1);
      match &inner[0] {
        Decl::Def(def) => assert_eq!(def.name.to_string(), "Ns.a"),
        other => panic!("expected inner Def, got {other:?}"),
      }
    }
    other => panic!("expected Generated, got {other:?}"),
  }
}

#[test]
fn test_with_block_dotted_prefix() {
  let s = r#"with Dotted.Name { def a : I64 := 1 }"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Generated(inner) => match &inner[0] {
      Decl::Def(def) => assert_eq!(def.name.to_string(), "Dotted.Name.a"),
      other => panic!("expected inner Def, got {other:?}"),
    },
    other => panic!("expected Generated, got {other:?}"),
  }
}

#[test]
fn test_with_block_prefixes_class_struct_instance() {
  let s = r#"with Ns {
    class K A { def m (x : A) : A }
    struct S { f : I64 }
    instance Inst : K I64 { def m (x : I64) : I64 := x }
  }"#
    .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Generated(inner) => {
      assert_eq!(inner.len(), 3);
      match &inner[0] {
        Decl::Type(ind) => assert_eq!(ind.name().to_string(), "Ns.K"),
        other => panic!("expected inner Type, got {other:?}"),
      }
      match &inner[1] {
        Decl::Type(ind) => assert_eq!(ind.name().to_string(), "Ns.S"),
        other => panic!("expected inner struct, got {other:?}"),
      }
      match &inner[2] {
        Decl::Ins(ins) => assert_eq!(ins.name().to_string(), "Ns.Inst"),
        other => panic!("expected inner Ins, got {other:?}"),
      }
    }
    other => panic!("expected Generated, got {other:?}"),
  }
}

#[test]
fn test_nested_with_composes_prefixes() {
  let s = r#"with A { with B { def c : I64 := 1 } }"#.into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Generated(outer) => {
      assert_eq!(outer.len(), 1);
      match &outer[0] {
        Decl::Generated(inner) => match &inner[0] {
          Decl::Def(def) => assert_eq!(def.name.to_string(), "A.B.c"),
          other => panic!("expected innermost Def, got {other:?}"),
        },
        other => panic!("expected nested Generated, got {other:?}"),
      }
    }
    other => panic!("expected Generated, got {other:?}"),
  }
}

/// `with` must match as a whole word: `withdraw` is an identifier, not a
/// block header (`terminated(tag("with"), ws1)`).
#[test]
fn test_with_keyword_requires_word_boundary() {
  let s = r#"withdraw the funds"#.into();
  // Either it fails to parse as a decl, or it parses as something that
  // is NOT a with block; both outcomes rule out a keyword steal.
  match decl_parser(s) {
    Err(_) => {}
    Ok((_, res)) => assert!(not_a_with_block(res.value())),
  }
}

fn not_a_with_block(d: &Decl) -> bool {
  !matches!(d, Decl::Generated(_))
}

/// An unclosed block fails the decl parse rather than silently
/// consuming the rest of the file.
#[test]
fn test_with_block_unclosed_fails() {
  let s = r#"with Ns { def a : I64 := 1"#.into();
  assert!(decl_parser(s).is_err());
}

/// The prelude's real shape: attributed BODY-LESS defs inside the block.
/// A body-less def parses on the host only through the marker-attribute
/// paths (`#[native]`/`#[export]`/`#[extern]`/`#[cubical]`), so this pins
/// that the block's inner decl loop reaches them.
#[test]
fn test_with_block_accepts_attributed_bodyless_decls() {
  let s = r#"with Cubical {
    #[cubical "interval"] def I : Type
    #[cubical "i0"] def i0 : Cubical.I
  }"#
    .into();
  let (_, res) = decl_parser(s).unwrap();
  match res.value() {
    Decl::Generated(inner) => {
      assert_eq!(inner.len(), 2);
      match &inner[0] {
        Decl::Def(def) => assert_eq!(def.name.to_string(), "Cubical.I"),
        other => panic!("expected inner Def, got {other:?}"),
      }
      match &inner[1] {
        Decl::Def(def) => assert_eq!(def.name.to_string(), "Cubical.i0"),
        other => panic!("expected inner Def, got {other:?}"),
      }
    }
    other => panic!("expected Generated, got {other:?}"),
  }
}
