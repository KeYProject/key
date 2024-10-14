#![allow(internal_features)]
#![allow(rustc::internal)]

mod callbacks;
mod hir;

pub use hir::conversion::convert;

use hir::Crate;
use rustc_driver_impl::RunCompiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};

pub fn start() -> Crate {
    let dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    rustc_driver_impl::init_rustc_env_logger(&dcx);
    let mut callbacks = callbacks::Wrapper::new();
    RunCompiler::new(&[], &mut callbacks).run().unwrap();
    callbacks.result()
}
