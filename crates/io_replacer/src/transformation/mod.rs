use super::*;

mod close;
mod fflush;
mod fgetc;
mod fgets;
mod fileno;
mod flockfile;
mod fopen;
mod fprintf;
mod fputc;
mod fputs;
mod fread;
mod fscanf;
mod fseek;
mod fwrite;
mod getdelim;
mod hir_ctx;
mod popen;
mod stream_ty;
pub mod transform;
mod visitor;

fn unwrap_paren(e: &rustc_ast::Expr) -> &rustc_ast::Expr {
    if let rustc_ast::ExprKind::Paren(e) = &e.kind {
        unwrap_paren(e)
    } else {
        e
    }
}
