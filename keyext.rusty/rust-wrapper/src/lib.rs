#![allow(internal_features)]
#![allow(rustc::internal)]

use jni::{
    objects::{JClass, JObject},
    JNIEnv,
};

mod callbacks;
mod hir;

pub use hir::conversion::convert;

use hir::Crate;
use rustc_driver_impl::RunCompiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};

#[no_mangle]
pub extern "system" fn Java_org_key_1project_rusty_nast_Wrapper_start<'a>(
    mut env: JNIEnv<'a>,
    _class: JClass<'a>,
) -> JObject<'a> {
    let c = start();
    let crate_class = env
        .find_class("org/key_project/rusty/nast/Wrapper$Crate")
        .expect("could not find Crate class");
    let ret = env
        .alloc_object(crate_class)
        .expect("Could not allocate crate");
    return ret;
}

pub fn start() -> Crate {
    let dcx = EarlyDiagCtxt::new(ErrorOutputType::default());

    rustc_driver_impl::init_rustc_env_logger(&dcx);
    let mut callbacks = callbacks::Wrapper::new();
    RunCompiler::new(&[], &mut callbacks).run().unwrap();
    callbacks.result()
}
