use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

pub struct Wrapper {}

impl Wrapper {
    pub fn new() -> Self {
        Wrapper {}
    }
}

impl Callbacks for Wrapper {
    fn after_analysis<'tcx>(&mut self, _: &Compiler, q: &'tcx Queries<'tcx>) -> Compilation {
        Compilation::Continue
    }
}
