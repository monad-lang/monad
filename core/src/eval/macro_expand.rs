use crate::term::module::LoadedModules;
use crate::term::{Decl, SourceContext};

/// Maximum macro expansion depth to prevent infinite recursion
const MAX_EXPANSION_DEPTH: u64 = 64;

/// Error type for macro expansion failures
#[derive(Debug, Clone)]
pub enum MacroError {
  DepthLimitExceeded,
  NonTermReturn { name: String },
  MacroNotFound { name: String },
  Generic(String),
}

impl std::fmt::Display for MacroError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MacroError::DepthLimitExceeded => write!(f, "macro expansion depth limit exceeded"),
      MacroError::NonTermReturn { name } => {
        write!(f, "macro `{name}` did not return a Term value")
      }
      MacroError::MacroNotFound { name } => {
        write!(f, "macro `{name}` not found")
      }
      MacroError::Generic(msg) => write!(f, "{msg}"),
    }
  }
}

/// Expand all macro calls in declarations.
/// Runs between elaboration and type checking.
pub fn expand_macros(
  decls: Vec<SourceContext<Decl>>,
  _loaded: &LoadedModules,
) -> Result<Vec<SourceContext<Decl>>, MacroError> {
  // TODO: implement macro expansion
  Ok(decls)
}
