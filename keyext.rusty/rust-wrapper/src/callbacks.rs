use rustc_driver_impl::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

use crate::{convert, hir::Crate};

pub struct Wrapper {
    converted: Option<Crate>,
}

impl Wrapper {
    pub fn new() -> Self {
        Wrapper { converted: None }
    }

    pub fn result(self) -> Crate {
        self.converted.unwrap()
    }
}

impl Callbacks for Wrapper {
    fn after_analysis<'tcx>(&mut self, _: &Compiler, q: &'tcx Queries<'tcx>) -> Compilation {
        q.global_ctxt().unwrap().enter(|tcx| {
            self.converted = Some(convert(tcx));
        });
        Compilation::Continue
    }
}
