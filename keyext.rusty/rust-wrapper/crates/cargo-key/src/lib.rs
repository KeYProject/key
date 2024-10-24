use clap::Parser;
use key_wrapper::options::{Options, OutputFile};
use serde::{Deserialize, Serialize};

#[derive(Parser, Serialize, Deserialize)]
#[command(version, author)]
pub struct WrapperArgs {
    /// Print to stdout.
    #[clap(group = "output", long)]
    stdout: bool,
    /// Print to a file.
    #[clap(group = "output", long, short, env)]
    output_file: Option<String>,
    /// Pretty print the output
    #[clap(long)]
    pretty_print: bool,
}

impl WrapperArgs {
    pub fn to_options(self) -> Options {
        let output_file = match (self.stdout, self.output_file) {
            (true, _) => Some(OutputFile::Stdout),
            (_, Some(f)) => Some(OutputFile::File(f)),
            _ => None,
        };

        Options {
            output_file,
            pretty_print: self.pretty_print,
        }
    }
}

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub key: WrapperArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}
