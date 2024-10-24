use std::fs;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

use crate::{
    convert,
    hir::Crate,
    options::{Options, OutputFile},
};

pub struct Wrapper {
    converted: Option<Crate>,
    options: Options,
}

impl Wrapper {
    pub fn new(options: Options) -> Self {
        Wrapper {
            converted: None,
            options,
        }
    }

    pub fn result(self) -> Crate {
        self.converted.unwrap()
    }

    pub fn print(&self) {
        let Some(out) = &self.options.output_file else {
            return;
        };
        let krate = self
            .converted
            .as_ref()
            .expect("`print` called before crate was converted");
        let json = if self.options.pretty_print {
            serde_json::to_string_pretty(krate)
        } else {
            serde_json::to_string(krate)
        }
        .expect("serialization error");

        match out {
            OutputFile::File(file) => fs::write(file, json).expect("writing failed"),
            OutputFile::Stdout => println!("{json}"),
        }
    }
}

impl Callbacks for Wrapper {
    fn after_analysis<'tcx>(&mut self, _: &Compiler, q: &'tcx Queries<'tcx>) -> Compilation {
        q.global_ctxt().unwrap().enter(|tcx| {
            self.converted = Some(convert(tcx));
            self.print();
        });
        Compilation::Stop
    }
}
