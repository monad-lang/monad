// jsgen's library root -- bare `use jsgen` resolves here.
//
// The whole surface is the JS AST (`Js.Expr`, `Js.Stmt`, `Js.Module`) and
// its renderer. Constructors stay reachable through their type namespace
// (`Js.Expr.string`); no helpers are exported.

pub use lib::js {
    Js.Expr, Js.Stmt, Js.Module,
    Js.render_expr, Js.render_stmt, Js.render_stmts, Js.render_module,
    Js.string_literal, Js.valid_ident,
}
