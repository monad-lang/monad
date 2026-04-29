use crate::ir::function::LLVMFunction;

#[derive(Clone, Debug)]
pub struct LLVMGlobal {
    pub name: String,
    pub value: String,
    pub is_constant: bool,
}

impl LLVMGlobal {
    pub fn string(name: &str, content: &str) -> Self {
        let escaped = content
            .replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\n', "\\0A")
            .replace('\r', "\\0D")
            .replace('\t', "\\09");
        LLVMGlobal {
            name: name.to_string(),
            value: format!("c\"{}\\00\"", escaped),
            is_constant: true,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LLVMDeclaration {
    pub name: String,
    pub params: Vec<String>,
    pub return_type: String,
}

#[derive(Clone, Debug)]
pub struct LLVMModule {
    pub target_triple: String,
    pub globals: Vec<LLVMGlobal>,
    pub functions: Vec<LLVMFunction>,
    pub declarations: Vec<LLVMDeclaration>,
}

impl LLVMModule {
    pub fn new() -> Self {
        LLVMModule {
            target_triple: "x86_64-unknown-linux-gnu".to_string(),
            globals: vec![],
            functions: vec![],
            declarations: vec![],
        }
    }

    pub fn add_function(&mut self, func: LLVMFunction) {
        self.functions.push(func);
    }

    pub fn add_global(&mut self, global: LLVMGlobal) {
        self.globals.push(global);
    }

    pub fn add_declaration(&mut self, decl: LLVMDeclaration) {
        self.declarations.push(decl);
    }

    pub fn emit(&self) -> String {
        let mut output = String::new();
        self.emit_to(&mut output).unwrap();
        output
    }

    pub fn emit_to(&self, f: &mut dyn std::fmt::Write) -> std::fmt::Result {
        writeln!(f, "; ModuleID = 'monad'")?;
        writeln!(f, "target triple = \"{}\"", self.target_triple)?;
        writeln!(f)?;

        writeln!(f, "; === Type Definitions ===")?;
        writeln!(f, "%Header = type {{ i64, i16, i16 }}")?;
        writeln!(
            f,
            "%Closure = type {{ %Header, i8*, i64, i64, [0 x i8*] }}"
        )?;
        writeln!(
            f,
            "%Constructor = type {{ %Header, i64, i64, [0 x i8*] }}"
        )?;
        writeln!(f, "%StringObj = type {{ %Header, i64, [0 x i8] }}")?;
        writeln!(f)?;

        writeln!(f, "; === External Declarations ===")?;
        writeln!(f, "declare i8* @monad_alloc(i64)")?;
        writeln!(f, "declare void @monad_retain(i8*)")?;
        writeln!(f, "declare void @monad_release(i8*)")?;
        writeln!(f, "declare void @monad_print_i64(i64)")?;
        writeln!(f, "declare void @monad_print_str(i8*)")?;
        writeln!(f, "declare %Closure* @alloc_closure(i8*, i64, i64)")?;
        writeln!(
            f,
            "declare %Constructor* @alloc_constructor(i64, i64)"
        )?;
        writeln!(f, "declare %StringObj* @alloc_string(i8*, i64)")?;
        writeln!(f)?;

        for decl in &self.declarations {
            writeln!(
                f,
                "declare {} @{}({})",
                decl.return_type,
                decl.name,
                decl.params.join(", ")
            )?;
        }
        if !self.declarations.is_empty() {
            writeln!(f)?;
        }

        writeln!(f, "; === Globals ===")?;
        for global in &self.globals {
            if global.is_constant {
                writeln!(
                    f,
                    "@{} = constant [{} x i8] c\"{}\"",
                    global.name,
                    global.value.len(),
                    global.value
                )?;
            } else {
                writeln!(f, "@{} = global {}", global.name, global.value)?;
            }
        }
        if !self.globals.is_empty() {
            writeln!(f)?;
        }

        writeln!(f, "; === Functions ===")?;
        for func in &self.functions {
            func.emit_to(f)?;
            writeln!(f)?;
        }

        Ok(())
    }
}
