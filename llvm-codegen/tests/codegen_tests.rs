use monad_core::term::{Decl, Param, Term, def, id, lam, lams, mpt, num, param, type0};

use monad_llvm_codegen::compile_decls;

fn make_def(name: &str, params: Vec<Param>, body: Term) -> Decl {
    let param_types: Vec<Term> = params.iter().map(|p| (*p.typ).clone()).collect();
    let full_type = if param_types.is_empty() {
        type0()
    } else {
        let mut typ = type0();
        for pt in param_types.into_iter().rev() {
            typ = Term::Pi {
                arg_name: None,
                arg: Box::new(pt),
                ret: Box::new(typ),
            };
        }
        typ
    };
    let term = if params.is_empty() {
        body
    } else {
        lams(params.clone(), body)
    };
    Decl::Def(def(mpt(name), vec![], full_type, term, vec![]))
}

#[test]
fn test_compile_integer_literal() {
    let body = num(42);
    let decls = vec![make_def("main", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("define cc 9 i64 @main()"));
    assert!(output.contains("ret i64 42"));
    assert!(output.contains("cc 9"));
}

#[test]
fn test_compile_lambda() {
    let body = Term::Var {
        name: monad_core::term::NameRef::Id(id("x")),
    };
    let decls = vec![make_def("identity", vec![param(id("x"), type0())], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("define cc 9 i64 @identity(i64 %p0)"));
    assert!(output.contains("ret i64"));
}

#[test]
fn test_compile_multiple_functions() {
    let body1 = num(10);
    let body2 = num(20);
    let decls = vec![
        make_def("foo", vec![], body1),
        make_def("bar", vec![], body2),
    ];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("define cc 9 i64 @foo()"));
    assert!(output.contains("define cc 9 i64 @bar()"));
    assert!(output.contains("ret i64 10"));
    assert!(output.contains("ret i64 20"));
}

#[test]
fn test_compile_with_main_wrapper() {
    let body = num(42);
    let decls = vec![make_def("main", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("define i32 @main(i32 %argc, i64 %argv)"));
    assert!(output.contains("ret i32 0"));
}

#[test]
fn test_llvm_ir_has_type_definitions() {
    let body = num(1);
    let decls = vec![make_def("test", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("%Header = type"));
    assert!(output.contains("%Closure = type"));
    assert!(output.contains("%Constructor = type"));
    assert!(output.contains("%StringObj = type"));
}

#[test]
fn test_llvm_ir_has_runtime_declarations() {
    let body = num(1);
    let decls = vec![make_def("test", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("declare i8* @monad_alloc(i64)"));
    assert!(output.contains("declare void @monad_retain(i8*)"));
    assert!(output.contains("declare void @monad_release(i8*)"));
    assert!(output.contains("declare void @monad_print_i64(i64)"));
}

#[test]
fn test_ghc_calling_convention() {
    let body = num(1);
    let decls = vec![make_def("test", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("cc 9"));
}

#[test]
fn test_compile_nested_lambdas() {
    let inner_body = Term::Var {
        name: monad_core::term::NameRef::Id(id("x")),
    };
    let inner_lam = lam(param(id("x"), type0()), inner_body);
    let outer_body = Term::App {
        fun: Box::new(inner_lam),
        arg: Box::new(num(42)),
    };
    let decls = vec![make_def("test", vec![], outer_body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("define cc 9 i64 @test()"));
}

#[test]
fn test_compile_string_literal() {
    let body = Term::Lit {
        value: monad_core::term::Literal::Str {
            value: "hello".to_string(),
        },
    };
    let decls = vec![make_def("greet", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    assert!(output.contains("@str_"));
    assert!(output.contains("constant"));
}

#[test]
fn test_generated_llvm_ir_is_valid() {
    let body = num(42);
    let decls = vec![make_def("test", vec![], body)];

    let module = compile_decls(&decls).unwrap();
    let output = module.emit();

    let temp_dir = std::env::temp_dir();
    let ll_path = temp_dir.join("monad_test.ll");
    let bc_path = temp_dir.join("monad_test.bc");

    std::fs::write(&ll_path, &output).unwrap();

    let status = std::process::Command::new("llvm-as")
        .arg(&ll_path)
        .arg("-o")
        .arg(&bc_path)
        .status();

    if let Ok(status) = status {
        assert!(status.success(), "llvm-as failed to parse generated IR");
        std::fs::remove_file(&ll_path).ok();
        std::fs::remove_file(&bc_path).ok();
    }
}
