#![feature(rustc_private)]

use std::{
    env,
    process::{exit, Command},
};

use cargo_key::Args;
use clap::Parser;

fn main() {
    let args = Args::parse_from(std::env::args().skip(1));

    let rml_rustc_path = env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("key-rustc");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = "check";

    let mut cmd = Command::new(cargo_path);
    //  println!("Rust flags: {:?}", &args.rust_flags);
    cmd.arg(cargo_cmd)
        .args(args.rust_flags)
        .env("RUSTC_WRAPPER", rml_rustc_path)
        .env("CARGO_INCREMENTAL", "0")
        .env("RUST_LOG", "debug")
        .env("RUST_BACKTRACE", "1");

    cmd.env("KEY_ARGS", serde_json::to_string(&args.key).unwrap());

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}
