use std::collections::HashMap;

use rustc_hir::BodyId;
use rustc_middle::ty::TyCtxt;

use super::{conversion::HirInto, visit::Visit, HirId, Mod, OwnerId, Ty};

pub fn extract_types(m: &Mod, tcx: TyCtxt) -> HashMap<HirId, Ty> {
    let mut c = Collector::new(tcx);
    c.visit_mod(m);
    c.map
}

struct Collector<'tcx> {
    map: HashMap<HirId, Ty>,
    last_body_id: Option<BodyId>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Collector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            map: Default::default(),
            last_body_id: None,
        }
    }
}

impl<'a, 'tcx> Visit<'a> for Collector<'tcx> {
    fn visit_body(&mut self, _: &'a super::Body) {
        let id = self
            .last_body_id
            .take()
            .expect("expected body id to be set");

        let owner: OwnerId = id.hir_id.expect_owner().into();

        let res = self.tcx.typeck_body(id);

        for (lid, ty) in res.node_types().items_in_stable_order() {
            let hir_id = HirId {
                owner: owner.clone(),
                local_id: lid.into(),
            };
            let ty: Ty = ty.hir_into(self.tcx);
            self.map.insert(hir_id, ty);
        }
    }
}
