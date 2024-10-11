#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod callbacks;
mod hir;

use rustc_driver::{RunCompiler, DEFAULT_LOCALE_RESOURCES};
use rustc_interface::interface::try_print_query_stack;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};

pub fn start() {
    let dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    rustc_driver::init_rustc_env_logger(&dcx);
    let mut callbacks = callbacks::Wrapper::new();
    RunCompiler::new(&[], &mut callbacks).run().unwrap()
}
