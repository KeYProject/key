#![feature(rustc_private)]

extern crate lazy_static;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_interface;
extern crate rustc_session;
extern crate termcolor;

use std::{env, panic, panic::PanicHookInfo, process::Command};

use cargo_key::{Args, WrapperArgs};
use clap::*;
use key_wrapper::callbacks::*;
use rustc_driver::{RunCompiler, DEFAULT_LOCALE_RESOURCES};
use rustc_errors::emitter::HumanEmitter;
use rustc_interface::interface::try_print_query_stack;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};
use termcolor::{ColorChoice, StandardStream};

const BUG_REPORT_URL: &str = "https://github.com/Drodt/TODO/issues/new";

lazy_static::lazy_static! {
    static ref ICE_HOOK: Box<dyn Fn(&panic::PanicHookInfo<'_>) + Sync + Send + 'static> = {
        let hook = panic::take_hook();
        panic::set_hook(Box::new(report_panic));
        hook
    };
}

fn report_panic(info: &PanicHookInfo) {
    (*ICE_HOOK)(info);

    // Separate the output with an empty line
    eprintln!();
    let fallback_bundle =
        rustc_errors::fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);

    let emitter = Box::new(HumanEmitter::new(
        Box::new(StandardStream::stderr(ColorChoice::Auto)),
        fallback_bundle,
    ));
    let diag_ctxt = rustc_errors::DiagCtxt::new(emitter);
    let handle = diag_ctxt.handle();

    let mut diagnostic = handle.struct_note("Wrapper has panic-ed!");
    diagnostic.note("Oops, that shouldn't have happened, sorry about that.");
    diagnostic.note(format!(
        "Please report this bug over here: {}",
        BUG_REPORT_URL
    ));

    diagnostic.emit();

    // If backtraces are enabled, also print the query stack
    let backtrace = env::var_os("RUST_BACKTRACE").map_or(false, |x| &x != "0");

    if backtrace {
        try_print_query_stack(handle, None, None);
    }
}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&handler);
    env_logger::init();
    lazy_static::initialize(&ICE_HOOK);

    setup_plugin();
}

fn setup_plugin() {
    let mut args = env::args().collect::<Vec<_>>();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }

    let key_args: WrapperArgs = if is_wrapper {
        serde_json::from_str(&std::env::var("KEY_ARGS").unwrap()).unwrap()
    } else {
        let all_args = Args::parse_from(&args);
        args = all_args.rust_flags;
        all_args.key
    };

    let sysroot = sysroot_path();
    args.push(format!("--sysroot={}", sysroot));

    args.push("-Cpanic=abort".to_owned());
    args.push("-Coverflow-checks=off".to_owned());
    args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    args.push("-Zcrate-attr=feature(rustc_attrs)".to_owned());
    args.push("-Zcrate-attr=feature(unsized_fn_params)".to_owned());

    let mut callbacks = Wrapper::new(key_args.to_options());

    RunCompiler::new(&args, &mut callbacks).run().unwrap();
}

fn sysroot_path() -> String {
    let toolchain: toml::Value =
        toml::from_str(include_str!("../../../../rust-toolchain.toml")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
