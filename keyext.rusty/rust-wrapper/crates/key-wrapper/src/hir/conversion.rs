use std::collections::HashMap;

use rustc_hir as hir;
use rustc_middle::ty::TyCtxt;
use rustc_span::{
    def_id::{DefIndex as HirDefIndex, LocalDefId as HirLocalDefId},
    symbol::Ident as HirIdent,
    BytePos as HirBytePos, Span as HirSpan, Symbol as HirSymbol,
};
use type_extract::extract_types;
use Ctor;
use Def;

use super::*;

pub fn convert(tcx: TyCtxt<'_>) -> Crate {
    let hir = tcx.hir();
    let m = hir.root_module();
    let top_mod = m.hir_into(tcx);
    let types = extract_types(&top_mod, tcx)
        .into_iter()
        .map(Into::into)
        .collect();
    Crate { top_mod, types }
}

pub struct ConversionCtxt<'tcx> {
    pub types: HashMap<HirId, Ty>,
    pub tcx: TyCtxt<'tcx>,
}

/// Allows translating from `T` to `Self`, where `T` is a HIR structure. Since
/// some structures reference bodies, we require access to the HIR.
pub trait FromHir<'hir, T>
where
    T: Sized,
{
    /// Translate from `value` to `Self`, where `T` is a HIR structure. Since
    /// some structures reference bodies, we require access to the HIR via
    /// `hir`.
    fn from_hir(value: T, tcx: TyCtxt<'hir>) -> Self;
}

/// Allows translating from `Self` to `T`, where `Self` is a HIR structure.
/// Since some structures reference bodies, we require access to the HIR.
///
/// **Do not implement this directly.** Use [FromHir] instead.
pub trait HirInto<'hir, T>
where
    T: Sized,
{
    /// Translate from `self` to `T`, where `self` is a HIR structure. Since
    /// some structures reference bodies, we require access to the HIR via
    /// `hir`.
    fn hir_into(self, tcx: TyCtxt<'hir>) -> T;
}

impl<'hir, T, U> HirInto<'hir, U> for T
where
    U: FromHir<'hir, T>,
    T: std::fmt::Debug,
{
    fn hir_into(self, tcx: TyCtxt<'hir>) -> U {
        U::from_hir(self, tcx)
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Mod<'hir>> for Mod {
    fn from_hir(value: &'hir hir::Mod<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Mod {
            spans: value.spans.into(),
            items: value
                .item_ids
                .iter()
                .map(|id| tcx.hir().item(*id).hir_into(tcx))
                .collect(),
        }
    }
}

impl From<hir::ModSpans> for ModSpans {
    fn from(value: hir::ModSpans) -> Self {
        ModSpans {
            inner_span: value.inner_span.into(),
            inject_use_span: value.inject_use_span.into(),
        }
    }
}

impl From<HirSpan> for Span {
    fn from(value: HirSpan) -> Self {
        Span {
            lo: value.lo().into(),
            hi: value.hi().into(),
            //ctxt: value.ctxt().into(),
            parent: value.parent().map(|p| p.into()),
        }
    }
}

impl From<HirBytePos> for BytePos {
    fn from(value: HirBytePos) -> Self {
        BytePos(value.0)
    }
}

impl From<HirLocalDefId> for LocalDefId {
    fn from(value: HirLocalDefId) -> Self {
        LocalDefId {
            local_def_index: value.local_def_index.into(),
        }
    }
}

impl From<HirDefIndex> for DefIndex {
    fn from(value: HirDefIndex) -> Self {
        DefIndex(value.as_u32())
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Item<'hir>> for Item {
    fn from_hir(value: &'hir hir::Item<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Item {
            ident: value.ident.into(),
            owner_id: value.owner_id.into(),
            kind: (&value.kind).hir_into(tcx),
            span: value.span.into(),
            vis_span: value.vis_span.into(),
        }
    }
}

impl From<HirIdent> for Ident {
    fn from(value: HirIdent) -> Self {
        Ident {
            name: value.name.into(),
            span: value.span.into(),
        }
    }
}

impl From<HirSymbol> for Symbol {
    fn from(value: HirSymbol) -> Self {
        Symbol(value.to_ident_string())
    }
}

impl From<&HirSymbol> for Symbol {
    fn from(value: &HirSymbol) -> Self {
        Symbol(value.to_ident_string())
    }
}

impl From<hir::OwnerId> for OwnerId {
    fn from(value: hir::OwnerId) -> Self {
        OwnerId {
            def_id: value.def_id.into(),
        }
    }
}

impl<'hir> FromHir<'hir, Vec<hir::def::Res>> for Vec<Res> {
    fn from_hir(value: Vec<hir::def::Res>, tcx: TyCtxt<'hir>) -> Self {
        let mut res = Vec::with_capacity(value.len());
        for i in value {
            res.push(i.hir_into(tcx));
        }
        res
    }
}

impl<'hir> FromHir<'hir, hir::def::Res> for Res {
    fn from_hir(value: hir::def::Res, _: TyCtxt<'hir>) -> Self {
        match value {
            rustc_hir::def::Res::Def(def_kind, def_id) => Self::Def {
                def: Def {
                    kind: (&def_kind).into(),
                    id: (&def_id).into(),
                },
            },
            rustc_hir::def::Res::PrimTy(prim_ty) => Self::PrimTy {
                ty: (&prim_ty).into(),
            },
            rustc_hir::def::Res::SelfTyParam { trait_ } => Self::SelfTyParam {
                trait_: (&trait_).into(),
            },
            rustc_hir::def::Res::SelfTyAlias {
                alias_to,
                forbid_generic,
                is_trait_impl,
            } => Self::SelfTyAlias {
                alias_to: (&alias_to).into(),
                forbid_generic: forbid_generic,
                is_trait_impl: is_trait_impl,
            },
            rustc_hir::def::Res::SelfCtor(def_id) => Self::SelfCtor((&def_id).into()),
            rustc_hir::def::Res::Local(id) => Self::Local { id: id.into() },
            rustc_hir::def::Res::ToolMod => Self::ToolMod,
            rustc_hir::def::Res::NonMacroAttr(non_macro_attr_kind) => {
                Self::NonMacroAttr((&non_macro_attr_kind).into())
            }
            rustc_hir::def::Res::Err => Self::Err,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ItemKind<'hir>> for ItemKind {
    fn from_hir(value: &'hir hir::ItemKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::ItemKind::ExternCrate(symbol) => ItemKind::ExternCrate {
                symbol: symbol.map(|s| s.into()),
            },
            hir::ItemKind::Use(path, use_kind) => ItemKind::Use {
                path: Path {
                    span: path.span.into(),
                    res: path.res.clone().into_vec().hir_into(tcx),
                    segments: path.segments.iter().map(|s| s.hir_into(tcx)).collect(),
                },
                use_kind: use_kind.into(),
            },
            hir::ItemKind::Static(hir_ty, m, body) => Self::Static {
                ty: (*hir_ty).hir_into(tcx),
                r#const: matches!(m, hir::Mutability::Mut),
                body: tcx.hir().body(*body).hir_into(tcx),
            },
            hir::ItemKind::Const(hir_ty, generics, body) => Self::Const {
                ty: (*hir_ty).hir_into(tcx),
                generics: (*generics).hir_into(tcx),
                body: tcx.hir().body(*body).hir_into(tcx),
            },
            hir::ItemKind::Fn(fn_sig, generics, body) => Self::Fn {
                sig: fn_sig.hir_into(tcx),
                generics: (*generics).hir_into(tcx),
                body_id: body.clone(),
                body: tcx.hir().body(*body).hir_into(tcx),
            },
            hir::ItemKind::Mod(m) => Self::Mod {
                r#mod: (*m).hir_into(tcx),
            },
            hir::ItemKind::TyAlias(hir_ty, generics) => Self::TyAlias {
                ty: (*hir_ty).hir_into(tcx),
                generics: (*generics).hir_into(tcx),
            },
            hir::ItemKind::Enum(enum_def, generics) => Self::Enum {
                def: enum_def.hir_into(tcx),
                generics: (*generics).hir_into(tcx),
            },
            hir::ItemKind::Struct(data, generics) => Self::Struct {
                data: data.hir_into(tcx),
                generics: (*generics).hir_into(tcx),
            },
            hir::ItemKind::Union(data, generics) => Self::Union {
                data: data.hir_into(tcx),
                generics: (*generics).hir_into(tcx),
            },
            hir::ItemKind::Trait(auto, safe, generics, bounds, refs) => Self::Trait {
                field1: matches!(auto, hir::IsAuto::Yes),
                field2: matches!(safe, hir::Safety::Safe),
                generics: (*generics).hir_into(tcx),
                bounds: (*bounds).hir_into(tcx),
                refs: refs.iter().map(Into::into).collect(),
            },
            hir::ItemKind::TraitAlias(generics, bounds) => Self::TraitAlias {
                generics: (*generics).hir_into(tcx),
                bounds: (*bounds).hir_into(tcx),
            },
            hir::ItemKind::Impl(i) => Self::Impl {
                r#impl: (*i).hir_into(tcx),
            },
            hir::ItemKind::Macro(..) => todo!("Macro"),
            hir::ItemKind::ForeignMod { .. } => todo!("ForeignMod"),
            hir::ItemKind::GlobalAsm(..) => todo!("Asm"),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::FnSig<'hir>> for FnSig {
    fn from_hir(value: &'hir hir::FnSig<'hir>, tcx: TyCtxt<'hir>) -> Self {
        FnSig {
            header: value.header.into(),
            decl: value.decl.hir_into(tcx),
            span: value.span.into(),
        }
    }
}

impl From<hir::FnHeader> for FnHeader {
    fn from(value: hir::FnHeader) -> Self {
        FnHeader {
            safety: matches!(value.safety, hir::Safety::Safe),
            constness: matches!(value.constness, hir::Constness::Const),
            asyncness: matches!(value.asyncness, hir::IsAsync::Async(_)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::EnumDef<'hir>> for EnumDef {
    fn from_hir(value: &'hir hir::EnumDef<'hir>, tcx: TyCtxt<'hir>) -> Self {
        EnumDef {
            variants: value.variants.hir_into(tcx),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Variant<'hir>> for Variant {
    fn from_hir(value: &'hir hir::Variant<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Variant {
            ident: value.ident.into(),
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            data: (&value.data).hir_into(tcx),
            disr_expr: value.disr_expr.map(|e| e.hir_into(tcx)),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::VariantData<'hir>> for VariantData {
    fn from_hir(value: &'hir hir::VariantData<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::VariantData::Struct { fields, recovered } => Self::Struct {
                fields: (*fields).hir_into(tcx),
                recovered: matches!(recovered, rustc_ast::Recovered::Yes(_)),
            },
            hir::VariantData::Tuple(fs, hir_id, lid) => {
                Self::Tuple((*fs).hir_into(tcx), hir_id.into(), (*lid).into())
            }
            hir::VariantData::Unit(hir_id, lid) => Self::Unit(hir_id.into(), (*lid).into()),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::FieldDef<'hir>> for FieldDef {
    fn from_hir(value: &'hir hir::FieldDef<'hir>, tcx: TyCtxt<'hir>) -> Self {
        FieldDef {
            span: value.span.into(),
            vis_span: value.vis_span.into(),
            ident: value.ident.into(),
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            ty: value.ty.hir_into(tcx),
        }
    }
}

impl From<&hir::TraitItemRef> for TraitItemRef {
    fn from(value: &hir::TraitItemRef) -> Self {
        TraitItemRef {
            id: value.id.into(),
            ident: value.ident.into(),
            kind: value.kind.into(),
            span: value.span.into(),
        }
    }
}

impl From<hir::TraitItemId> for TraitItemId {
    fn from(value: hir::TraitItemId) -> Self {
        TraitItemId {
            owner_id: value.owner_id.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Impl<'hir>> for Impl {
    fn from_hir(value: &'hir hir::Impl<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Impl {
            constness: matches!(value.constness, hir::Constness::Const),
            safety: matches!(value.safety, hir::Safety::Safe),
            polarity: value.polarity.into(),
            defaultness: value.defaultness.into(),
            defaultness_span: value.defaultness_span.map(Into::into),
            generics: value.generics.hir_into(tcx),
            of_trait: value.of_trait.as_ref().map(|t| (t).hir_into(tcx)),
            self_ty: value.self_ty.hir_into(tcx),
            items: value.items.hir_into(tcx),
        }
    }
}

impl From<hir::ImplPolarity> for ImplPolarity {
    fn from(value: hir::ImplPolarity) -> Self {
        match value {
            hir::ImplPolarity::Negative(sp) => Self::Negative(sp.into()),
            _ => Self::Positive,
        }
    }
}

impl From<hir::Defaultness> for Defaultness {
    fn from(value: hir::Defaultness) -> Self {
        match value {
            hir::Defaultness::Default { has_value } => Self::Default { has_value },
            _ => Self::Final,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Generics<'hir>> for Generics {
    fn from_hir(value: &'hir hir::Generics<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Generics {
            params: value.params.hir_into(tcx),
            predicates: value.predicates.hir_into(tcx),
            has_where_clause_predicates: value.has_where_clause_predicates,
            where_clause_span: value.where_clause_span.into(),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::WherePredicate<'hir>> for WherePredicate {
    fn from_hir(value: &'hir hir::WherePredicate<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::WherePredicate::BoundPredicate(b) => Self::Bound(b.hir_into(tcx)),
            hir::WherePredicate::RegionPredicate(r) => Self::Region(r.hir_into(tcx)),
            hir::WherePredicate::EqPredicate(e) => Self::Eq(e.hir_into(tcx)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::WhereBoundPredicate<'hir>> for WhereBoundPredicate {
    fn from_hir(value: &'hir hir::WhereBoundPredicate<'hir>, tcx: TyCtxt<'hir>) -> Self {
        WhereBoundPredicate {
            hir_id: value.hir_id.into(),
            span: value.span.into(),
            origin: value.origin.into(),
            bound_generic_params: value.bound_generic_params.hir_into(tcx),
            bounded_ty: value.bounded_ty.hir_into(tcx),
            bounds: value.bounds.hir_into(tcx),
        }
    }
}

impl From<hir::PredicateOrigin> for PredicateOrigin {
    fn from(value: hir::PredicateOrigin) -> Self {
        match value {
            hir::PredicateOrigin::WhereClause => Self::WhereClause,
            hir::PredicateOrigin::GenericParam => Self::GenericParam,
            hir::PredicateOrigin::ImplTrait => Self::ImplTrait,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::WhereRegionPredicate<'hir>> for WhereRegionPredicate {
    fn from_hir(value: &'hir hir::WhereRegionPredicate<'hir>, tcx: TyCtxt<'hir>) -> Self {
        WhereRegionPredicate {
            span: value.span.into(),
            in_where_clause: value.in_where_clause,
            lifetime: value.lifetime.into(),
            bounds: value.bounds.hir_into(tcx),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::WhereEqPredicate<'hir>> for WhereEqPredicate {
    fn from_hir(value: &'hir hir::WhereEqPredicate<'hir>, tcx: TyCtxt<'hir>) -> Self {
        WhereEqPredicate {
            span: value.span.into(),
            lhs_ty: value.lhs_ty.hir_into(tcx),
            rhs_ty: value.rhs_ty.hir_into(tcx),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ImplItemRef> for ImplItemRef {
    fn from_hir(value: &'hir hir::ImplItemRef, _: TyCtxt<'hir>) -> Self {
        ImplItemRef {
            id: value.id.into(),
            ident: value.ident.into(),
            kind: value.kind.into(),
            span: value.span.into(),
            trait_item_def_id: value.trait_item_def_id.map(|d| (&d).into()),
        }
    }
}

impl From<hir::ImplItemId> for ImplItemId {
    fn from(value: hir::ImplItemId) -> Self {
        ImplItemId {
            owner_id: value.owner_id.into(),
        }
    }
}

impl From<hir::AssocItemKind> for AssocItemKind {
    fn from(value: hir::AssocItemKind) -> Self {
        match value {
            hir::AssocItemKind::Const => Self::Const,
            hir::AssocItemKind::Fn { has_self } => Self::Fn { has_self },
            hir::AssocItemKind::Type => Self::Type,
        }
    }
}

impl<'hir, R, T> FromHir<'hir, &'hir hir::Path<'hir, R>> for Path<T>
where
    T: FromHir<'hir, &'hir R>,
    R: std::fmt::Debug,
{
    fn from_hir(value: &'hir hir::Path<'hir, R>, tcx: TyCtxt<'hir>) -> Self {
        Path {
            span: value.span.into(),
            res: (&value.res).hir_into(tcx),
            segments: value.segments.iter().map(|s| s.hir_into(tcx)).collect(),
        }
    }
}

/* impl<'hir> FromHir<'hir, &'hir [hir::def::Res]> for Vec<Res> {
    fn from_hir(value: &'hir [hir::def::Res], tcx: TyCtxt<'hir>) -> Self {
        todo!()
    }
} */

impl From<&hir::UseKind> for UseKind {
    fn from(value: &hir::UseKind) -> Self {
        match value {
            hir::UseKind::Single => UseKind::Single,
            hir::UseKind::Glob => UseKind::Glob,
            hir::UseKind::ListStem => UseKind::ListStem,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PathSegment<'hir>> for PathSegment {
    fn from_hir(value: &'hir hir::PathSegment<'hir>, tcx: TyCtxt<'hir>) -> Self {
        PathSegment {
            ident: value.ident.into(),
            hir_id: value.hir_id.into(),
            res: value.res.into(),
            args: value.args.map(|a| a.hir_into(tcx)),
            infer_args: value.infer_args,
        }
    }
}

impl From<hir::HirId> for HirId {
    fn from(value: hir::HirId) -> Self {
        (&value).into()
    }
}

impl From<&hir::HirId> for HirId {
    fn from(value: &hir::HirId) -> Self {
        HirId {
            owner: value.owner.into(),
            local_id: value.local_id.into(),
        }
    }
}

impl From<hir::ItemLocalId> for ItemLocalId {
    fn from(value: hir::ItemLocalId) -> Self {
        ItemLocalId(value.as_u32())
    }
}

impl From<hir::def::Res> for Res {
    fn from(value: hir::def::Res) -> Self {
        match &value {
            hir::def::Res::Def(kind, id) => Self::Def {
                def: Def {
                    kind: kind.into(),
                    id: id.into(),
                },
            },
            hir::def::Res::PrimTy(ty) => Self::PrimTy { ty: ty.into() },
            hir::def::Res::SelfTyParam { trait_ } => Self::SelfTyParam {
                trait_: trait_.into(),
            },
            hir::def::Res::SelfTyAlias {
                alias_to,
                forbid_generic,
                is_trait_impl,
            } => Self::SelfTyAlias {
                alias_to: alias_to.into(),
                forbid_generic: *forbid_generic,
                is_trait_impl: *is_trait_impl,
            },
            hir::def::Res::SelfCtor(id) => Self::SelfCtor(id.into()),
            hir::def::Res::Local(id) => Self::Local { id: id.into() },
            hir::def::Res::ToolMod => Self::ToolMod,
            hir::def::Res::NonMacroAttr(kind) => Self::NonMacroAttr(kind.into()),
            hir::def::Res::Err => Self::Err,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericArgs<'hir>> for GenericArgs {
    fn from_hir(value: &'hir hir::GenericArgs<'hir>, tcx: TyCtxt<'hir>) -> Self {
        GenericArgs {
            args: value.args.hir_into(tcx),
            constraints: value.constraints.hir_into(tcx),
            parenthesized: value.parenthesized.into(),
            span_ext: value.span_ext.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericArg<'hir>> for GenericArg {
    fn from_hir(value: &'hir hir::GenericArg<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::GenericArg::Lifetime(l) => Self::Lifetime((*l).into()),
            hir::GenericArg::Type(ty) => Self::Type((*ty).hir_into(tcx)),
            hir::GenericArg::Const(c) => Self::Const((*c).hir_into(tcx)),
            hir::GenericArg::Infer(i) => Self::Infer(i.into()),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::AssocItemConstraint<'hir>> for AssocItemConstraint {
    fn from_hir(value: &'hir hir::AssocItemConstraint<'hir>, tcx: TyCtxt<'hir>) -> Self {
        AssocItemConstraint {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            gen_args: value.gen_args.hir_into(tcx),
            kind: (&value.kind).hir_into(tcx),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::AssocItemConstraintKind<'hir>> for AssocItemConstraintKind {
    fn from_hir(value: &'hir hir::AssocItemConstraintKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::AssocItemConstraintKind::Equality { term } => AssocItemConstraintKind::Equality {
                term: term.hir_into(tcx),
            },
            hir::AssocItemConstraintKind::Bound { bounds } => AssocItemConstraintKind::Bound {
                bounds: (*bounds).hir_into(tcx),
            },
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Term<'hir>> for Term {
    fn from_hir(value: &'hir hir::Term<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::Term::Ty(ty) => Self::Ty((*ty).hir_into(tcx)),
            hir::Term::Const(c) => Self::Const((*c).hir_into(tcx)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericBound<'hir>> for GenericBound {
    fn from_hir(value: &'hir hir::GenericBound<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::GenericBound::Trait(r) => GenericBound::Trait(r.hir_into(tcx)),
            hir::GenericBound::Outlives(l) => GenericBound::Outlives((*l).into()),
            hir::GenericBound::Use(args, sp) => Self::Use((*args).hir_into(tcx), (*sp).into()),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PreciseCapturingArg<'hir>> for PreciseCapturingArg {
    fn from_hir(value: &'hir hir::PreciseCapturingArg<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::PreciseCapturingArg::Lifetime(l) => Self::Lifetime((*l).into()),
            hir::PreciseCapturingArg::Param(a) => Self::Param(a.hir_into(tcx)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PreciseCapturingNonLifetimeArg>
    for PreciseCapturingNonLifetimeArg
{
    fn from_hir(value: &'hir hir::PreciseCapturingNonLifetimeArg, tcx: TyCtxt<'hir>) -> Self {
        PreciseCapturingNonLifetimeArg {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            res: (&value.res).hir_into(tcx),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PolyTraitRef<'hir>> for PolyTraitRef {
    fn from_hir(value: &'hir hir::PolyTraitRef<'hir>, tcx: TyCtxt<'hir>) -> Self {
        PolyTraitRef {
            bound_generic_params: value.bound_generic_params.hir_into(tcx),
            trait_ref: (&value.trait_ref).hir_into(tcx),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::TraitRef<'hir>> for TraitRef {
    fn from_hir(value: &'hir hir::TraitRef<'hir>, tcx: TyCtxt<'hir>) -> Self {
        TraitRef {
            path: value.path.hir_into(tcx),
            hir_ref_id: value.hir_ref_id.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericParam<'hir>> for GenericParam {
    fn from_hir(value: &'hir hir::GenericParam<'hir>, tcx: TyCtxt<'hir>) -> Self {
        GenericParam {
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            name: value.name.into(),
            span: value.span.into(),
            pure_wrt_drop: value.pure_wrt_drop,
            kind: (&value.kind).hir_into(tcx),
            colon_span: value.colon_span.map(Into::into),
            source: value.source.into(),
        }
    }
}

impl From<hir::ParamName> for ParamName {
    fn from(value: hir::ParamName) -> Self {
        match value {
            hir::ParamName::Plain(ident) => Self::Plain(ident.into()),
            hir::ParamName::Fresh => Self::Fresh,
            hir::ParamName::Error => Self::Error,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericParamKind<'hir>> for GenericParamKind {
    fn from_hir(value: &'hir hir::GenericParamKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::GenericParamKind::Lifetime { kind } => Self::Lifetime { kind: kind.into() },
            hir::GenericParamKind::Type { default, synthetic } => Self::Type {
                default: default.map(|ty| ty.hir_into(tcx)),
                synthetic: *synthetic,
            },
            hir::GenericParamKind::Const {
                ty,
                default,
                is_host_effect,
                synthetic,
            } => Self::Const {
                ty: (*ty).hir_into(tcx),
                default: default.map(|d| d.hir_into(tcx)),
                is_host_effect: *is_host_effect,
                synthetic: *synthetic,
            },
        }
    }
}

impl From<&hir::LifetimeParamKind> for LifetimeParamKind {
    fn from(value: &hir::LifetimeParamKind) -> Self {
        match value {
            hir::LifetimeParamKind::Explicit => Self::Explicit,
            hir::LifetimeParamKind::Elided(kind) => Self::Elided(kind.into()),
            hir::LifetimeParamKind::Error => Self::Error,
        }
    }
}

impl From<&hir::MissingLifetimeKind> for MissingLifetimeKind {
    fn from(value: &hir::MissingLifetimeKind) -> Self {
        match value {
            hir::MissingLifetimeKind::Underscore => Self::Underscore,
            hir::MissingLifetimeKind::Ampersand => Self::Ampersand,
            hir::MissingLifetimeKind::Comma => Self::Comma,
            hir::MissingLifetimeKind::Brackets => Self::Brackets,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ConstArg<'hir>> for ConstArg {
    fn from_hir(value: &'hir hir::ConstArg<'hir>, tcx: TyCtxt<'hir>) -> Self {
        ConstArg {
            hir_id: value.hir_id.into(),
            kind: (&value.kind).hir_into(tcx),
            is_desugared_from_effects: value.is_desugared_from_effects,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ConstArgKind<'hir>> for ConstArgKind {
    fn from_hir(value: &'hir hir::ConstArgKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::ConstArgKind::Path(qpath) => Self::Path(qpath.hir_into(tcx)),
            hir::ConstArgKind::Anon(anon_const) => Self::Anon((*anon_const).hir_into(tcx)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::QPath<'hir>> for QPath {
    fn from_hir(value: &'hir hir::QPath<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::QPath::Resolved(ty, p) => Self::Resolved {
                ty: ty.map(|t| t.hir_into(tcx)),
                path: (*p).hir_into(tcx),
            },
            hir::QPath::TypeRelative(ty, seg) => Self::TypeRelative {
                ty: (*ty).hir_into(tcx),
                seg: (*seg).hir_into(tcx),
            },
            hir::QPath::LangItem(li, sp) => Self::LangItem {
                item: li.into(),
                span: (*sp).into(),
            },
        }
    }
}

impl From<&hir::LangItem> for LangItem {
    fn from(value: &hir::LangItem) -> Self {
        match value {
            hir::LangItem::Sized => Self::Sized,
            hir::LangItem::Unsize => Self::Unsize,
            hir::LangItem::StructuralPeq => Self::StructuralPeq,
            hir::LangItem::Copy => Self::Copy,
            hir::LangItem::Clone => Self::Clone,
            hir::LangItem::CloneFn => Self::CloneFn,
            hir::LangItem::Sync => Self::Sync,
            hir::LangItem::DiscriminantKind => Self::DiscriminantKind,
            hir::LangItem::Discriminant => Self::Discriminant,
            hir::LangItem::PointeeTrait => Self::PointeeTrait,
            hir::LangItem::Metadata => Self::Metadata,
            hir::LangItem::DynMetadata => Self::DynMetadata,
            hir::LangItem::Freeze => Self::Freeze,
            hir::LangItem::FnPtrTrait => Self::FnPtrTrait,
            hir::LangItem::FnPtrAddr => Self::FnPtrAddr,
            hir::LangItem::Drop => Self::Drop,
            hir::LangItem::Destruct => Self::Destruct,
            hir::LangItem::AsyncDrop => Self::AsyncDrop,
            hir::LangItem::AsyncDestruct => Self::AsyncDestruct,
            hir::LangItem::AsyncDropInPlace => Self::AsyncDropInPlace,
            hir::LangItem::SurfaceAsyncDropInPlace => Self::SurfaceAsyncDropInPlace,
            hir::LangItem::AsyncDropSurfaceDropInPlace => Self::AsyncDropSurfaceDropInPlace,
            hir::LangItem::AsyncDropSlice => Self::AsyncDropSlice,
            hir::LangItem::AsyncDropChain => Self::AsyncDropChain,
            hir::LangItem::AsyncDropNoop => Self::AsyncDropNoop,
            hir::LangItem::AsyncDropDeferredDropInPlace => Self::AsyncDropDeferredDropInPlace,
            hir::LangItem::AsyncDropFuse => Self::AsyncDropFuse,
            hir::LangItem::AsyncDropDefer => Self::AsyncDropDefer,
            hir::LangItem::AsyncDropEither => Self::AsyncDropEither,
            hir::LangItem::CoerceUnsized => Self::CoerceUnsized,
            hir::LangItem::DispatchFromDyn => Self::DispatchFromDyn,
            hir::LangItem::TransmuteOpts => Self::TransmuteOpts,
            hir::LangItem::TransmuteTrait => Self::TransmuteTrait,
            hir::LangItem::Add => Self::Add,
            hir::LangItem::Sub => Self::Sub,
            hir::LangItem::Mul => Self::Mul,
            hir::LangItem::Div => Self::Div,
            hir::LangItem::Rem => Self::Rem,
            hir::LangItem::Neg => Self::Neg,
            hir::LangItem::Not => Self::Not,
            hir::LangItem::BitXor => Self::BitXor,
            hir::LangItem::BitAnd => Self::BitAnd,
            hir::LangItem::BitOr => Self::BitOr,
            hir::LangItem::Shl => Self::Shl,
            hir::LangItem::Shr => Self::Shr,
            hir::LangItem::AddAssign => Self::AddAssign,
            hir::LangItem::SubAssign => Self::SubAssign,
            hir::LangItem::MulAssign => Self::MulAssign,
            hir::LangItem::DivAssign => Self::DivAssign,
            hir::LangItem::RemAssign => Self::RemAssign,
            hir::LangItem::BitXorAssign => Self::BitXorAssign,
            hir::LangItem::BitAndAssign => Self::BitAndAssign,
            hir::LangItem::BitOrAssign => Self::BitOrAssign,
            hir::LangItem::ShlAssign => Self::ShlAssign,
            hir::LangItem::ShrAssign => Self::ShrAssign,
            hir::LangItem::Index => Self::Index,
            hir::LangItem::IndexMut => Self::IndexMut,
            hir::LangItem::UnsafeCell => Self::UnsafeCell,
            hir::LangItem::VaList => Self::VaList,
            hir::LangItem::Deref => Self::Deref,
            hir::LangItem::DerefMut => Self::DerefMut,
            hir::LangItem::DerefPure => Self::DerefPure,
            hir::LangItem::DerefTarget => Self::DerefTarget,
            hir::LangItem::Receiver => Self::Receiver,
            hir::LangItem::Fn => Self::Fn,
            hir::LangItem::FnMut => Self::FnMut,
            hir::LangItem::FnOnce => Self::FnOnce,
            hir::LangItem::AsyncFn => Self::AsyncFn,
            hir::LangItem::AsyncFnMut => Self::AsyncFnMut,
            hir::LangItem::AsyncFnOnce => Self::AsyncFnOnce,
            hir::LangItem::AsyncFnOnceOutput => Self::AsyncFnOnceOutput,
            hir::LangItem::CallOnceFuture => Self::CallOnceFuture,
            hir::LangItem::CallRefFuture => Self::CallRefFuture,
            hir::LangItem::AsyncFnKindHelper => Self::AsyncFnKindHelper,
            hir::LangItem::AsyncFnKindUpvars => Self::AsyncFnKindUpvars,
            hir::LangItem::FnOnceOutput => Self::FnOnceOutput,
            hir::LangItem::Iterator => Self::Iterator,
            hir::LangItem::FusedIterator => Self::FusedIterator,
            hir::LangItem::Future => Self::Future,
            hir::LangItem::FutureOutput => Self::FutureOutput,
            hir::LangItem::AsyncIterator => Self::AsyncIterator,
            hir::LangItem::CoroutineState => Self::CoroutineState,
            hir::LangItem::Coroutine => Self::Coroutine,
            hir::LangItem::CoroutineReturn => Self::CoroutineReturn,
            hir::LangItem::CoroutineYield => Self::CoroutineYield,
            hir::LangItem::CoroutineResume => Self::CoroutineResume,
            hir::LangItem::Unpin => Self::Unpin,
            hir::LangItem::Pin => Self::Pin,
            hir::LangItem::OrderingEnum => Self::OrderingEnum,
            hir::LangItem::PartialEq => Self::PartialEq,
            hir::LangItem::PartialOrd => Self::PartialOrd,
            hir::LangItem::CVoid => Self::CVoid,
            hir::LangItem::Panic => Self::Panic,
            hir::LangItem::PanicNounwind => Self::PanicNounwind,
            hir::LangItem::PanicFmt => Self::PanicFmt,
            hir::LangItem::ConstPanicFmt => Self::ConstPanicFmt,
            hir::LangItem::PanicBoundsCheck => Self::PanicBoundsCheck,
            hir::LangItem::PanicMisalignedPointerDereference => {
                Self::PanicMisalignedPointerDereference
            }
            hir::LangItem::PanicInfo => Self::PanicInfo,
            hir::LangItem::PanicLocation => Self::PanicLocation,
            hir::LangItem::PanicImpl => Self::PanicImpl,
            hir::LangItem::PanicCannotUnwind => Self::PanicCannotUnwind,
            hir::LangItem::PanicInCleanup => Self::PanicInCleanup,
            hir::LangItem::PanicAddOverflow => Self::PanicAddOverflow,
            hir::LangItem::PanicSubOverflow => Self::PanicSubOverflow,
            hir::LangItem::PanicMulOverflow => Self::PanicMulOverflow,
            hir::LangItem::PanicDivOverflow => Self::PanicDivOverflow,
            hir::LangItem::PanicRemOverflow => Self::PanicRemOverflow,
            hir::LangItem::PanicNegOverflow => Self::PanicNegOverflow,
            hir::LangItem::PanicShrOverflow => Self::PanicShrOverflow,
            hir::LangItem::PanicShlOverflow => Self::PanicShlOverflow,
            hir::LangItem::PanicDivZero => Self::PanicDivZero,
            hir::LangItem::PanicRemZero => Self::PanicRemZero,
            hir::LangItem::PanicCoroutineResumed => Self::PanicCoroutineResumed,
            hir::LangItem::PanicAsyncFnResumed => Self::PanicAsyncFnResumed,
            hir::LangItem::PanicAsyncGenFnResumed => Self::PanicAsyncGenFnResumed,
            hir::LangItem::PanicGenFnNone => Self::PanicGenFnNone,
            hir::LangItem::PanicCoroutineResumedPanic => Self::PanicCoroutineResumedPanic,
            hir::LangItem::PanicAsyncFnResumedPanic => Self::PanicAsyncFnResumedPanic,
            hir::LangItem::PanicAsyncGenFnResumedPanic => Self::PanicAsyncGenFnResumedPanic,
            hir::LangItem::PanicGenFnNonePanic => Self::PanicGenFnNonePanic,
            hir::LangItem::BeginPanic => Self::BeginPanic,
            hir::LangItem::FormatAlignment => Self::FormatAlignment,
            hir::LangItem::FormatArgument => Self::FormatArgument,
            hir::LangItem::FormatArguments => Self::FormatArguments,
            hir::LangItem::FormatCount => Self::FormatCount,
            hir::LangItem::FormatPlaceholder => Self::FormatPlaceholder,
            hir::LangItem::FormatUnsafeArg => Self::FormatUnsafeArg,
            hir::LangItem::ExchangeMalloc => Self::ExchangeMalloc,
            hir::LangItem::DropInPlace => Self::DropInPlace,
            hir::LangItem::FallbackSurfaceDrop => Self::FallbackSurfaceDrop,
            hir::LangItem::AllocLayout => Self::AllocLayout,
            hir::LangItem::Start => Self::Start,
            hir::LangItem::EhPersonality => Self::EhPersonality,
            hir::LangItem::EhCatchTypeinfo => Self::EhCatchTypeinfo,
            hir::LangItem::OwnedBox => Self::OwnedBox,
            hir::LangItem::GlobalAlloc => Self::GlobalAlloc,
            hir::LangItem::PtrUnique => Self::PtrUnique,
            hir::LangItem::PhantomData => Self::PhantomData,
            hir::LangItem::ManuallyDrop => Self::ManuallyDrop,
            hir::LangItem::MaybeUninit => Self::MaybeUninit,
            hir::LangItem::AlignOffset => Self::AlignOffset,
            hir::LangItem::Termination => Self::Termination,
            hir::LangItem::Try => Self::Try,
            hir::LangItem::Tuple => Self::Tuple,
            hir::LangItem::SliceLen => Self::SliceLen,
            hir::LangItem::TryTraitFromResidual => Self::TryTraitFromResidual,
            hir::LangItem::TryTraitFromOutput => Self::TryTraitFromOutput,
            hir::LangItem::TryTraitBranch => Self::TryTraitBranch,
            hir::LangItem::TryTraitFromYeet => Self::TryTraitFromYeet,
            hir::LangItem::PointerLike => Self::PointerLike,
            hir::LangItem::ConstParamTy => Self::ConstParamTy,
            hir::LangItem::UnsizedConstParamTy => Self::UnsizedConstParamTy,
            hir::LangItem::Poll => Self::Poll,
            hir::LangItem::PollReady => Self::PollReady,
            hir::LangItem::PollPending => Self::PollPending,
            hir::LangItem::AsyncGenReady => Self::AsyncGenReady,
            hir::LangItem::AsyncGenPending => Self::AsyncGenPending,
            hir::LangItem::AsyncGenFinished => Self::AsyncGenFinished,
            hir::LangItem::ResumeTy => Self::ResumeTy,
            hir::LangItem::GetContext => Self::GetContext,
            hir::LangItem::Context => Self::Context,
            hir::LangItem::FuturePoll => Self::FuturePoll,
            hir::LangItem::AsyncIteratorPollNext => Self::AsyncIteratorPollNext,
            hir::LangItem::IntoAsyncIterIntoIter => Self::IntoAsyncIterIntoIter,
            hir::LangItem::Option => Self::Option,
            hir::LangItem::OptionSome => Self::OptionSome,
            hir::LangItem::OptionNone => Self::OptionNone,
            hir::LangItem::ResultOk => Self::ResultOk,
            hir::LangItem::ResultErr => Self::ResultErr,
            hir::LangItem::ControlFlowContinue => Self::ControlFlowContinue,
            hir::LangItem::ControlFlowBreak => Self::ControlFlowBreak,
            hir::LangItem::IntoFutureIntoFuture => Self::IntoFutureIntoFuture,
            hir::LangItem::IntoIterIntoIter => Self::IntoIterIntoIter,
            hir::LangItem::IteratorNext => Self::IteratorNext,
            hir::LangItem::PinNewUnchecked => Self::PinNewUnchecked,
            hir::LangItem::RangeFrom => Self::RangeFrom,
            hir::LangItem::RangeFull => Self::RangeFull,
            hir::LangItem::RangeInclusiveStruct => Self::RangeInclusiveStruct,
            hir::LangItem::RangeInclusiveNew => Self::RangeInclusiveNew,
            hir::LangItem::Range => Self::Range,
            hir::LangItem::RangeToInclusive => Self::RangeToInclusive,
            hir::LangItem::RangeTo => Self::RangeTo,
            hir::LangItem::String => Self::String,
            hir::LangItem::CStr => Self::CStr,
            hir::LangItem::EffectsRuntime => Self::EffectsRuntime,
            hir::LangItem::EffectsNoRuntime => Self::EffectsNoRuntime,
            hir::LangItem::EffectsMaybe => Self::EffectsMaybe,
            hir::LangItem::EffectsIntersection => Self::EffectsIntersection,
            hir::LangItem::EffectsIntersectionOutput => Self::EffectsIntersectionOutput,
            hir::LangItem::EffectsCompat => Self::EffectsCompat,
            hir::LangItem::EffectsTyCompat => Self::EffectsTyCompat,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Ty<'hir>> for HirTy {
    fn from_hir(value: &'hir hir::Ty<'hir>, tcx: TyCtxt<'hir>) -> Self {
        HirTy {
            hir_id: value.hir_id.into(),
            kind: Box::new((&value.kind).hir_into(tcx)),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::TyKind<'hir>> for HirTyKind {
    fn from_hir(value: &'hir hir::TyKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::TyKind::InferDelegation(id, kind) => Self::InferDelegation {
                def_id: id.into(),
                kind: kind.into(),
            },
            hir::TyKind::Slice(ty) => Self::Slice {
                ty: (*ty).hir_into(tcx),
            },
            hir::TyKind::Array(ty, l) => Self::Array {
                ty: (*ty).hir_into(tcx),
                len: l.hir_into(tcx),
            },
            hir::TyKind::Ptr(ty) => Self::Ptr {
                ty: ty.hir_into(tcx),
            },
            hir::TyKind::Ref(l, ty) => Self::Ref {
                lifetime: (*l).into(),
                ty: ty.hir_into(tcx),
            },
            hir::TyKind::BareFn(ty) => Self::BareFn {
                ty: (*ty).hir_into(tcx),
            },
            hir::TyKind::Never => Self::Never,
            hir::TyKind::Tup(tys) => Self::Tup {
                tys: (*tys).hir_into(tcx),
            },
            hir::TyKind::AnonAdt(id) => Self::AnonAdt {
                item: tcx.hir().item(*id).hir_into(tcx),
            },
            hir::TyKind::Path(path) => Self::Path {
                path: path.hir_into(tcx),
            },
            hir::TyKind::OpaqueDef(..) => {
                todo!("OpagueDef")
            }
            hir::TyKind::TraitObject(ts, l, syn) => Self::TraitObject {
                refs: ts.iter().map(|r| r.hir_into(tcx)).collect(),
                lifetime: (*l).into(),
                syntax: syn.into(),
            },
            hir::TyKind::Typeof(c) => Self::Typeof {
                r#const: (*c).hir_into(tcx),
            },
            hir::TyKind::Infer => Self::Infer,
            hir::TyKind::Err(_) => Self::Err,
            hir::TyKind::Pat(ty, p) => Self::Pat {
                ty: (*ty).hir_into(tcx),
                pat: (*p).hir_into(tcx),
            },
        }
    }
}

impl From<&hir::InferDelegationKind> for InferDelegationKind {
    fn from(value: &hir::InferDelegationKind) -> Self {
        match value {
            hir::InferDelegationKind::Output => Self::Output,
            hir::InferDelegationKind::Input(n) => Self::Input(*n),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::MutTy<'hir>> for MutHirTy {
    fn from_hir(value: &'hir hir::MutTy<'hir>, tcx: TyCtxt<'hir>) -> Self {
        MutHirTy {
            ty: value.ty.hir_into(tcx),
            mutbl: matches!(value.mutbl, hir::Mutability::Mut),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::BareFnTy<'hir>> for BareFnHirTy {
    fn from_hir(value: &'hir hir::BareFnTy<'hir>, tcx: TyCtxt<'hir>) -> Self {
        BareFnHirTy {
            safety: matches!(value.safety, hir::Safety::Safe),
            generic_params: value.generic_params.hir_into(tcx),
            decl: value.decl.hir_into(tcx),
            param_names: value.param_names.iter().copied().map(Into::into).collect(),
        }
    }
}

impl From<&rustc_ast::TraitObjectSyntax> for TraitObjectSyntax {
    fn from(value: &rustc_ast::TraitObjectSyntax) -> Self {
        match value {
            rustc_ast::TraitObjectSyntax::Dyn => Self::Dyn,
            rustc_ast::TraitObjectSyntax::DynStar => Self::DynStar,
            rustc_ast::TraitObjectSyntax::None => Self::None,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::def::Res> for Res {
    fn from_hir(value: &'hir hir::def::Res, _: TyCtxt<'hir>) -> Self {
        match value {
            hir::def::Res::Def(kind, id) => Self::Def {
                def: Def {
                    kind: kind.into(),
                    id: id.into(),
                },
            },
            hir::def::Res::PrimTy(ty) => Self::PrimTy { ty: ty.into() },
            hir::def::Res::SelfTyParam { trait_ } => Self::SelfTyParam {
                trait_: trait_.into(),
            },
            hir::def::Res::SelfTyAlias {
                alias_to,
                forbid_generic,
                is_trait_impl,
            } => Self::SelfTyAlias {
                alias_to: alias_to.into(),
                forbid_generic: *forbid_generic,
                is_trait_impl: *is_trait_impl,
            },
            hir::def::Res::SelfCtor(id) => Self::SelfCtor(id.into()),
            hir::def::Res::Local(id) => Self::Local { id: id.into() },
            hir::def::Res::ToolMod => Self::ToolMod,
            hir::def::Res::NonMacroAttr(kind) => Self::NonMacroAttr(kind.into()),
            hir::def::Res::Err => Self::Err,
        }
    }
}

impl From<&hir::def::DefKind> for DefKind {
    fn from(value: &hir::def::DefKind) -> Self {
        match value {
            hir::def::DefKind::Mod => Self::Mod,
            hir::def::DefKind::Struct => Self::Struct,
            hir::def::DefKind::Union => Self::Union,
            hir::def::DefKind::Enum => Self::Enum,
            hir::def::DefKind::Variant => Self::Variant,
            hir::def::DefKind::Trait => Self::Trait,
            hir::def::DefKind::TyAlias => Self::TyAlias,
            hir::def::DefKind::ForeignTy => Self::ForeignTy,
            hir::def::DefKind::TraitAlias => Self::TraitAlias,
            hir::def::DefKind::AssocTy => Self::AssocTy,
            hir::def::DefKind::TyParam => Self::TyParam,
            hir::def::DefKind::Fn => Self::Fn,
            hir::def::DefKind::Const => Self::Const,
            hir::def::DefKind::ConstParam => Self::ConstParam,
            hir::def::DefKind::Static {
                safety: hir::Safety::Safe,
                mutability: hir::Mutability::Mut,
                nested,
            } => Self::Static {
                safety: true,
                mutability: true,
                nested: *nested,
            },
            hir::def::DefKind::Static {
                safety: hir::Safety::Safe,
                mutability: hir::Mutability::Not,
                nested,
            } => Self::Static {
                safety: true,
                mutability: false,
                nested: *nested,
            },
            hir::def::DefKind::Static {
                safety: hir::Safety::Unsafe,
                mutability: hir::Mutability::Mut,
                nested,
            } => Self::Static {
                safety: false,
                mutability: true,
                nested: *nested,
            },
            hir::def::DefKind::Static {
                safety: hir::Safety::Unsafe,
                mutability: hir::Mutability::Not,
                nested,
            } => Self::Static {
                safety: false,
                mutability: false,
                nested: *nested,
            },
            hir::def::DefKind::Ctor(of, hir::def::CtorKind::Fn) => {
                Self::Ctor(Ctor(of.into(), true))
            }
            hir::def::DefKind::Ctor(of, hir::def::CtorKind::Const) => {
                Self::Ctor(Ctor(of.into(), false))
            }
            hir::def::DefKind::AssocFn => Self::AssocFn,
            hir::def::DefKind::AssocConst => Self::AssocConst,
            hir::def::DefKind::Macro(kind) => Self::Macro(kind.into()),
            hir::def::DefKind::ExternCrate => Self::ExternCrate,
            hir::def::DefKind::Use => Self::Use,
            hir::def::DefKind::ForeignMod => Self::ForeignMod,
            hir::def::DefKind::AnonConst => Self::AnonConst,
            hir::def::DefKind::InlineConst => Self::InlineConst,
            hir::def::DefKind::OpaqueTy => Self::OpaqueTy,
            hir::def::DefKind::Field => Self::Field,
            hir::def::DefKind::LifetimeParam => Self::LifetimeParam,
            hir::def::DefKind::GlobalAsm => Self::GlobalAsm,
            hir::def::DefKind::Impl { of_trait } => Self::Impl {
                of_trait: *of_trait,
            },
            hir::def::DefKind::Closure => Self::Closure,
            hir::def::DefKind::SyntheticCoroutineBody => Self::SyntheticCoroutineBody,
        }
    }
}

impl From<&hir::def::CtorOf> for CtorOf {
    fn from(value: &hir::def::CtorOf) -> Self {
        match value {
            hir::def::CtorOf::Struct => Self::Struct,
            hir::def::CtorOf::Variant => Self::Variant,
        }
    }
}

impl From<&rustc_span::MacroKind> for MacroKind {
    fn from(value: &rustc_span::MacroKind) -> Self {
        match value {
            rustc_span::MacroKind::Bang => Self::Bang,
            rustc_span::MacroKind::Attr => Self::Attr,
            rustc_span::MacroKind::Derive => Self::Derive,
        }
    }
}

impl From<&hir::PrimTy> for PrimHirTy {
    fn from(value: &hir::PrimTy) -> Self {
        match value {
            hir::PrimTy::Int(i) => Self::Int { ty: i.into() },
            hir::PrimTy::Uint(i) => Self::Uint { ty: i.into() },
            hir::PrimTy::Float(f) => Self::Float { ty: f.into() },
            hir::PrimTy::Str => Self::Str,
            hir::PrimTy::Bool => Self::Bool,
            hir::PrimTy::Char => Self::Char,
        }
    }
}

impl From<&rustc_ast::IntTy> for IntTy {
    fn from(value: &rustc_ast::IntTy) -> Self {
        match value {
            rustc_ast::IntTy::Isize => Self::Isize,
            rustc_ast::IntTy::I8 => Self::I8,
            rustc_ast::IntTy::I16 => Self::I16,
            rustc_ast::IntTy::I32 => Self::I32,
            rustc_ast::IntTy::I64 => Self::I64,
            rustc_ast::IntTy::I128 => Self::I128,
        }
    }
}

impl From<&rustc_ast::UintTy> for UintTy {
    fn from(value: &rustc_ast::UintTy) -> Self {
        match value {
            rustc_ast::UintTy::Usize => Self::Usize,
            rustc_ast::UintTy::U8 => Self::U8,
            rustc_ast::UintTy::U16 => Self::U16,
            rustc_ast::UintTy::U32 => Self::U32,
            rustc_ast::UintTy::U64 => Self::U64,
            rustc_ast::UintTy::U128 => Self::U128,
        }
    }
}

impl From<&rustc_ast::FloatTy> for FloatTy {
    fn from(value: &rustc_ast::FloatTy) -> Self {
        match value {
            rustc_ast::FloatTy::F16 => Self::F16,
            rustc_ast::FloatTy::F32 => Self::F32,
            rustc_ast::FloatTy::F64 => Self::F64,
            rustc_ast::FloatTy::F128 => Self::F128,
        }
    }
}

impl From<&rustc_span::def_id::DefId> for DefId {
    fn from(value: &rustc_span::def_id::DefId) -> Self {
        DefId {
            index: value.index.into(),
            krate: (&value.krate).into(),
        }
    }
}

impl From<&rustc_span::def_id::CrateNum> for CrateNum {
    fn from(value: &rustc_span::def_id::CrateNum) -> Self {
        CrateNum(value.as_u32())
    }
}

impl From<&hir::def::NonMacroAttrKind> for NonMacroAttrKind {
    fn from(value: &hir::def::NonMacroAttrKind) -> Self {
        match value {
            hir::def::NonMacroAttrKind::Builtin(s) => Self::Builtin(s.into()),
            hir::def::NonMacroAttrKind::Tool => Self::Tool,
            hir::def::NonMacroAttrKind::DeriveHelper => Self::DeriveHelper,
            hir::def::NonMacroAttrKind::DeriveHelperCompat => Self::DeriveHelperCompat,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::AnonConst> for AnonConst {
    fn from_hir(value: &'hir hir::AnonConst, tcx: TyCtxt<'hir>) -> Self {
        AnonConst {
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            body: tcx.hir().body(value.body).hir_into(tcx),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Body<'hir>> for Body {
    fn from_hir(value: &'hir hir::Body<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Body {
            params: value.params.hir_into(tcx),
            value: value.value.hir_into(tcx),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Param<'hir>> for Param {
    fn from_hir(value: &'hir hir::Param<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Param {
            hir_id: value.hir_id.into(),
            pat: value.pat.hir_into(tcx),
            ty_span: value.ty_span.into(),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Pat<'hir>> for Pat {
    fn from_hir(value: &'hir hir::Pat<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Pat {
            hir_id: value.hir_id.into(),
            kind: Box::new((&value.kind).hir_into(tcx)),
            span: value.span.into(),
            default_binding_modes: value.default_binding_modes,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PatKind<'hir>> for PatKind {
    fn from_hir(value: &'hir hir::PatKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::PatKind::Wild => Self::Wild,
            hir::PatKind::Binding(m, id, ident, p) => Self::Binding {
                mode: m.into(),
                hir_id: id.into(),
                ident: (*ident).into(),
                pat: p.map(|p| p.hir_into(tcx)),
            },
            hir::PatKind::Struct(path, fs, rest) => Self::Struct {
                path: path.hir_into(tcx),
                fields: (*fs).hir_into(tcx),
                rest: *rest,
            },
            hir::PatKind::TupleStruct(path, ps, ddp) => Self::TupleStruct {
                path: path.hir_into(tcx),
                pats: (*ps).hir_into(tcx),
                dot_dot_pos: ddp.into(),
            },
            hir::PatKind::Or(ps) => Self::Or {
                pats: (*ps).hir_into(tcx),
            },
            hir::PatKind::Never => Self::Never,
            hir::PatKind::Path(p) => Self::Path {
                path: p.hir_into(tcx),
            },
            hir::PatKind::Tuple(ps, ddp) => Self::Tuple {
                pats: (*ps).hir_into(tcx),
                dot_dot_pos: ddp.into(),
            },
            hir::PatKind::Box(p) => Self::Box {
                pat: (*p).hir_into(tcx),
            },
            hir::PatKind::Deref(p) => Self::Deref {
                pat: (*p).hir_into(tcx),
            },
            hir::PatKind::Ref(p, m) => Self::Ref {
                pat: (*p).hir_into(tcx),
                r#mut: matches!(m, hir::Mutability::Mut),
            },
            hir::PatKind::Lit(e) => Self::Lit {
                expr: (*e).hir_into(tcx),
            },
            hir::PatKind::Range(l, r, i) => Self::Range {
                lhs: l.map(|e| e.hir_into(tcx)),
                rhs: r.map(|e| e.hir_into(tcx)),
                inclusive: matches!(i, hir::RangeEnd::Included),
            },
            hir::PatKind::Slice(ps, p, pss) => Self::Slice {
                start: (*ps).hir_into(tcx),
                mid: p.map(|p| p.hir_into(tcx)),
                rest: (*pss).hir_into(tcx),
            },
            hir::PatKind::Err(_) => Self::Err,
        }
    }
}

impl From<&hir::BindingMode> for BindingMode {
    fn from(value: &hir::BindingMode) -> Self {
        BindingMode {
            by_ref: value.0.into(),
            r#mut: matches!(value.1, hir::Mutability::Mut),
        }
    }
}

impl From<hir::ByRef> for ByRef {
    fn from(value: hir::ByRef) -> Self {
        match value {
            hir::ByRef::Yes(hir::Mutability::Mut) => ByRef::Yes { r#mut: true },
            hir::ByRef::Yes(hir::Mutability::Not) => ByRef::Yes { r#mut: false },
            hir::ByRef::No => ByRef::No,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PatField<'hir>> for PatField {
    fn from_hir(value: &'hir hir::PatField<'hir>, tcx: TyCtxt<'hir>) -> Self {
        PatField {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            pat: value.pat.hir_into(tcx),
            is_shorthand: value.is_shorthand,
            span: value.span.into(),
        }
    }
}

impl From<&hir::DotDotPos> for DotDotPos {
    fn from(value: &hir::DotDotPos) -> Self {
        DotDotPos(match value.as_opt_usize() {
            Some(n) => n as u32,
            _ => u32::MAX,
        })
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Expr<'hir>> for Expr {
    fn from_hir(value: &'hir hir::Expr<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Expr {
            hir_id: value.hir_id.into(),
            kind: Box::new((&value.kind).hir_into(tcx)),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ExprKind<'hir>> for ExprKind {
    fn from_hir(value: &'hir hir::ExprKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::ExprKind::ConstBlock(c) => Self::ConstBlock {
                block: c.hir_into(tcx),
            },
            hir::ExprKind::Array(es) => Self::Array {
                exprs: (*es).hir_into(tcx),
            },
            hir::ExprKind::Call(e, es) => Self::Call {
                callee: (*e).hir_into(tcx),
                args: (*es).hir_into(tcx),
            },
            hir::ExprKind::MethodCall(p, e, es, sp) => Self::MethodCall {
                segment: (*p).hir_into(tcx),
                callee: (*e).hir_into(tcx),
                args: (*es).hir_into(tcx),
                span: (*sp).into(),
            },
            hir::ExprKind::Tup(es) => Self::Tup {
                exprs: (*es).hir_into(tcx),
            },
            hir::ExprKind::Binary(op, l, r) => Self::Binary {
                op: op.into(),
                left: (*l).hir_into(tcx),
                right: (*r).hir_into(tcx),
            },
            hir::ExprKind::Unary(op, e) => Self::Unary {
                op: op.into(),
                expr: (*e).hir_into(tcx),
            },
            hir::ExprKind::Lit(l) => Self::Lit { lit: (*l).into() },
            hir::ExprKind::Cast(e, ty) => Self::Cast {
                expr: (*e).hir_into(tcx),
                ty: (*ty).hir_into(tcx),
            },
            hir::ExprKind::Type(e, ty) => Self::Type {
                expr: (*e).hir_into(tcx),
                ty: (*ty).hir_into(tcx),
            },
            hir::ExprKind::DropTemps(e) => Self::DropTemps {
                expr: (*e).hir_into(tcx),
            },
            hir::ExprKind::Let(l) => Self::Let {
                r#let: (*l).hir_into(tcx),
            },
            hir::ExprKind::If(c, t, e) => Self::If {
                cond: (*c).hir_into(tcx),
                then: (*t).hir_into(tcx),
                els: e.map(|e| e.hir_into(tcx)),
            },
            hir::ExprKind::Loop(b, l, s, sp) => Self::Loop {
                block: (*b).hir_into(tcx),
                label: l.map(Into::into),
                src: s.into(),
                span: (*sp).into(),
            },
            hir::ExprKind::Match(e, arms, s) => Self::Match {
                expr: (*e).hir_into(tcx),
                arms: (*arms).hir_into(tcx),
                src: s.into(),
            },
            hir::ExprKind::Closure(c) => Self::Closure {
                closure: (*c).hir_into(tcx),
            },
            hir::ExprKind::Block(b, l) => Self::Block {
                block: (*b).hir_into(tcx),
                label: l.map(Into::into),
            },
            hir::ExprKind::Assign(l, r, sp) => Self::Assign {
                left: (*l).hir_into(tcx),
                right: (*r).hir_into(tcx),
                span: (*sp).into(),
            },
            hir::ExprKind::AssignOp(op, l, r) => Self::AssignOp {
                op: op.into(),
                left: (*l).hir_into(tcx),
                right: (*r).hir_into(tcx),
            },
            hir::ExprKind::Field(e, i) => Self::Field {
                expr: (*e).hir_into(tcx),
                field: (*i).into(),
            },
            hir::ExprKind::Index(b, i, sp) => Self::Index {
                base: (*b).hir_into(tcx),
                idx: (*i).hir_into(tcx),
                span: (*sp).into(),
            },
            hir::ExprKind::Path(p) => Self::Path {
                path: p.hir_into(tcx),
            },
            hir::ExprKind::AddrOf(raw, m, e) => Self::AddrOf {
                raw: matches!(raw, hir::BorrowKind::Raw),
                r#mut: matches!(m, hir::Mutability::Mut),
                expr: (*e).hir_into(tcx),
            },
            hir::ExprKind::Break(d, e) => Self::Break {
                dest: d.into(),
                expr: e.map(|e| e.hir_into(tcx)),
            },
            hir::ExprKind::Continue(d) => Self::Continue { dest: d.into() },
            hir::ExprKind::Ret(e) => Self::Ret {
                expr: e.map(|e| e.hir_into(tcx)),
            },
            hir::ExprKind::Become(e) => Self::Become {
                expr: (*e).hir_into(tcx),
            },
            hir::ExprKind::InlineAsm(..) => todo!("InlineAsm"),
            hir::ExprKind::OffsetOf(ty, is) => Self::OffsetOf {
                ty: (*ty).hir_into(tcx),
                idents: is.iter().copied().map(Into::into).collect(),
            },
            hir::ExprKind::Struct(path, fs, e) => Self::Struct {
                path: (*path).hir_into(tcx),
                fields: (*fs).hir_into(tcx),
                rest: e.map(|e| e.hir_into(tcx)),
            },
            hir::ExprKind::Repeat(e, l) => Self::Repeat {
                expr: (*e).hir_into(tcx),
                len: l.hir_into(tcx),
            },
            hir::ExprKind::Yield(e, s) => Self::Yield {
                expr: (*e).hir_into(tcx),
                src: s.into(),
            },
            hir::ExprKind::Err(_) => Self::Err,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ConstBlock> for ConstBlock {
    fn from_hir(value: &'hir hir::ConstBlock, tcx: TyCtxt<'hir>) -> Self {
        ConstBlock {
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            body: tcx.hir().body(value.body).hir_into(tcx),
        }
    }
}

impl From<&hir::UnOp> for UnOp {
    fn from(value: &hir::UnOp) -> Self {
        match value {
            hir::UnOp::Deref => Self::Deref,
            hir::UnOp::Not => Self::Not,
            hir::UnOp::Neg => Self::Neg,
        }
    }
}

impl From<&hir::Lit> for Lit {
    fn from(value: &hir::Lit) -> Self {
        Lit {
            node: (&value.node).into(),
            span: value.span.into(),
        }
    }
}

impl From<&rustc_ast::LitKind> for LitKind {
    fn from(value: &rustc_ast::LitKind) -> Self {
        match value {
            rustc_ast::LitKind::Str(sym, sty) => Self::Str {
                symbol: sym.into(),
                style: sty.into(),
            },
            rustc_ast::LitKind::ByteStr(bytes, sty) => Self::ByteStr {
                bytes: (*bytes).iter().copied().collect(),
                style: sty.into(),
            },
            rustc_ast::LitKind::CStr(bytes, sty) => Self::CStr {
                bytes: (*bytes).iter().copied().collect(),
                style: sty.into(),
            },
            rustc_ast::LitKind::Byte(b) => Self::Byte { byte: *b },
            rustc_ast::LitKind::Char(c) => Self::Char { char: *c },
            rustc_ast::LitKind::Int(v, ty) => Self::Int {
                value: v.0,
                ty: ty.into(),
            },
            rustc_ast::LitKind::Float(sym, ty) => Self::Float {
                symbol: sym.into(),
                ty: ty.into(),
            },
            rustc_ast::LitKind::Bool(b) => Self::Bool { value: *b },
            rustc_ast::LitKind::Err(_) => Self::Err,
        }
    }
}

impl From<&rustc_ast::StrStyle> for StrStyle {
    fn from(value: &rustc_ast::StrStyle) -> Self {
        match value {
            rustc_ast::StrStyle::Cooked => Self::Cooked,
            rustc_ast::StrStyle::Raw(c) => Self::Raw(*c),
        }
    }
}

impl From<&rustc_ast::LitIntType> for LitIntType {
    fn from(value: &rustc_ast::LitIntType) -> Self {
        match value {
            rustc_ast::LitIntType::Signed(ty) => Self::Signed { ty: ty.into() },
            rustc_ast::LitIntType::Unsigned(ty) => Self::Unsigned { ty: ty.into() },
            rustc_ast::LitIntType::Unsuffixed => Self::Unsuffixed,
        }
    }
}

impl From<&rustc_ast::LitFloatType> for LitFloatType {
    fn from(value: &rustc_ast::LitFloatType) -> Self {
        match value {
            rustc_ast::LitFloatType::Suffixed(ty) => Self::Suffixed(ty.into()),
            rustc_ast::LitFloatType::Unsuffixed => Self::Unsuffixed,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::LetExpr<'hir>> for LetExpr {
    fn from_hir(value: &'hir hir::LetExpr<'hir>, tcx: TyCtxt<'hir>) -> Self {
        LetExpr {
            span: value.span.into(),
            pat: value.pat.hir_into(tcx),
            ty: value.ty.map(|ty| ty.hir_into(tcx)),
            init: value.init.hir_into(tcx),
            recovered: matches!(value.recovered, rustc_ast::Recovered::Yes(_)),
        }
    }
}

impl From<&hir::LoopSource> for LoopSource {
    fn from(value: &hir::LoopSource) -> Self {
        match value {
            hir::LoopSource::Loop => Self::Loop,
            hir::LoopSource::While => Self::While,
            hir::LoopSource::ForLoop => Self::ForLoop,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Arm<'hir>> for Arm {
    fn from_hir(value: &'hir hir::Arm<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Arm {
            hir_id: value.hir_id.into(),
            span: value.span.into(),
            pat: value.pat.hir_into(tcx),
            guard: value.guard.map(|e| e.hir_into(tcx)),
            body: value.body.hir_into(tcx),
        }
    }
}

impl From<&hir::MatchSource> for MatchSource {
    fn from(value: &hir::MatchSource) -> Self {
        match value {
            hir::MatchSource::Normal => Self::Normal,
            hir::MatchSource::Postfix => Self::Postfix,
            hir::MatchSource::ForLoopDesugar => Self::ForLoopDesugar,
            hir::MatchSource::TryDesugar(id) => Self::TryDesugar(id.into()),
            hir::MatchSource::AwaitDesugar => Self::AwaitDesugar,
            hir::MatchSource::FormatArgs => Self::FormatArgs,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Closure<'hir>> for Closure {
    fn from_hir(value: &'hir hir::Closure<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Closure {
            def_id: value.def_id.into(),
            binder: value.binder.into(),
            constness: matches!(value.constness, hir::Constness::Const),
            capture_clause: value.capture_clause.into(),
            bound_generic_params: value.bound_generic_params.hir_into(tcx),
            fn_decl: value.fn_decl.hir_into(tcx),
            body: tcx.hir().body(value.body).hir_into(tcx),
            fn_decl_span: value.fn_decl_span.into(),
            fn_arg_span: value.fn_arg_span.map(Into::into),
        }
    }
}

impl From<hir::ClosureBinder> for ClosureBinder {
    fn from(value: hir::ClosureBinder) -> Self {
        match value {
            hir::ClosureBinder::For { span } => Self::For { span: span.into() },
            _ => Self::Default,
        }
    }
}

impl From<hir::CaptureBy> for CaptureBy {
    fn from(value: hir::CaptureBy) -> Self {
        match value {
            hir::CaptureBy::Value { move_kw } => Self::Value {
                move_kw: move_kw.into(),
            },
            _ => Self::Ref,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::FnDecl<'hir>> for FnDecl {
    fn from_hir(value: &'hir hir::FnDecl<'hir>, tcx: TyCtxt<'hir>) -> Self {
        FnDecl {
            inputs: value.inputs.hir_into(tcx),
            output: value.output.hir_into(tcx),
            c_variadic: value.c_variadic,
            implicit_self: value.implicit_self.into(),
            lifetime_elision_allowed: value.lifetime_elision_allowed,
        }
    }
}

impl<'hir> FromHir<'hir, hir::FnRetTy<'hir>> for FnRetTy {
    fn from_hir(value: hir::FnRetTy<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::FnRetTy::DefaultReturn(sp) => Self::DefaultReturn(sp.into()),
            hir::FnRetTy::Return(ty) => Self::Return(ty.hir_into(tcx)),
        }
    }
}

impl From<hir::ImplicitSelfKind> for ImplicitSelfKind {
    fn from(value: hir::ImplicitSelfKind) -> Self {
        match value {
            hir::ImplicitSelfKind::Imm => Self::Imm,
            hir::ImplicitSelfKind::Mut => Self::Mut,
            hir::ImplicitSelfKind::RefImm => Self::RefImm,
            hir::ImplicitSelfKind::RefMut => Self::RefMut,
            hir::ImplicitSelfKind::None => Self::None,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Block<'hir>> for Block {
    fn from_hir(value: &'hir hir::Block<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Block {
            stmts: value.stmts.hir_into(tcx),
            expr: value.expr.map(|e| e.hir_into(tcx)),
            hir_id: value.hir_id.into(),
            rules: value.rules.into(),
            span: value.span.into(),
            targeted_by_break: value.targeted_by_break,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Stmt<'hir>> for Stmt {
    fn from_hir(value: &'hir hir::Stmt<'hir>, tcx: TyCtxt<'hir>) -> Self {
        Stmt {
            hir_id: value.hir_id.into(),
            kind: (&value.kind).hir_into(tcx),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::StmtKind<'hir>> for StmtKind {
    fn from_hir(value: &'hir hir::StmtKind<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::StmtKind::Let(l) => Self::Let {
                r#let: (*l).hir_into(tcx),
            },
            hir::StmtKind::Item(i) => Self::Item {
                item: tcx.hir().item(*i).hir_into(tcx),
            },
            hir::StmtKind::Expr(e) => Self::Expr {
                expr: (*e).hir_into(tcx),
            },
            hir::StmtKind::Semi(e) => Self::Semi {
                expr: (*e).hir_into(tcx),
            },
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::LetStmt<'hir>> for LetStmt {
    fn from_hir(value: &'hir hir::LetStmt<'hir>, tcx: TyCtxt<'hir>) -> Self {
        LetStmt {
            pat: value.pat.hir_into(tcx),
            ty: value.ty.map(|ty| ty.hir_into(tcx)),
            init: value.init.map(|e| e.hir_into(tcx)),
            els: value.els.map(|b| b.hir_into(tcx)),
            hir_id: value.hir_id.into(),
            span: value.span.into(),
            source: value.source.into(),
        }
    }
}

impl From<hir::LocalSource> for LocalSource {
    fn from(value: hir::LocalSource) -> Self {
        match value {
            hir::LocalSource::Normal => Self::Normal,
            hir::LocalSource::AsyncFn => Self::AsyncFn,
            hir::LocalSource::AwaitDesugar => Self::AwaitDesugar,
            hir::LocalSource::AssignDesugar(sp) => Self::AssignDesugar { span: sp.into() },
        }
    }
}

impl From<hir::BlockCheckMode> for BlockCheckMode {
    fn from(value: hir::BlockCheckMode) -> Self {
        match value {
            hir::BlockCheckMode::DefaultBlock => Self::DefaultBlock,
            hir::BlockCheckMode::UnsafeBlock(s) => Self::UnsafeBlock { src: s.into() },
        }
    }
}

impl From<hir::UnsafeSource> for UnsafeSource {
    fn from(value: hir::UnsafeSource) -> Self {
        match value {
            hir::UnsafeSource::CompilerGenerated => Self::CompilerGenerated,
            hir::UnsafeSource::UserProvided => Self::UserProvided,
        }
    }
}

impl From<&hir::BinOp> for BinOp {
    fn from(value: &hir::BinOp) -> Self {
        BinOp {
            span: value.span.into(),
            node: value.node.into(),
        }
    }
}

impl From<hir::BinOpKind> for BinOpKind {
    fn from(value: hir::BinOpKind) -> Self {
        match value {
            hir::BinOpKind::Add => Self::Add,
            hir::BinOpKind::Sub => Self::Sub,
            hir::BinOpKind::Mul => Self::Mul,
            hir::BinOpKind::Div => Self::Div,
            hir::BinOpKind::Rem => Self::Rem,
            hir::BinOpKind::And => Self::And,
            hir::BinOpKind::Or => Self::Or,
            hir::BinOpKind::BitXor => Self::BitXor,
            hir::BinOpKind::BitAnd => Self::BitAnd,
            hir::BinOpKind::BitOr => Self::BitOr,
            hir::BinOpKind::Shl => Self::Shl,
            hir::BinOpKind::Shr => Self::Shr,
            hir::BinOpKind::Eq => Self::Eq,
            hir::BinOpKind::Lt => Self::Lt,
            hir::BinOpKind::Le => Self::Le,
            hir::BinOpKind::Ne => Self::Ne,
            hir::BinOpKind::Ge => Self::Ge,
            hir::BinOpKind::Gt => Self::Gt,
        }
    }
}

impl From<&hir::Destination> for Destination {
    fn from(value: &hir::Destination) -> Self {
        Destination {
            label: value.label.map(|l| l.into()),
            target_id: match value.target_id {
                Ok(id) => Ok(id.into()),
                Err(e) => Err(e.into()),
            },
        }
    }
}

impl From<rustc_ast::Label> for Label {
    fn from(value: rustc_ast::Label) -> Self {
        Label {
            ident: value.ident.into(),
        }
    }
}

impl From<hir::LoopIdError> for LoopIdError {
    fn from(value: hir::LoopIdError) -> Self {
        match value {
            hir::LoopIdError::OutsideLoopScope => Self::OutsideLoopScope,
            hir::LoopIdError::UnlabeledCfInWhileCondition => Self::UnlabeledCfInWhileCondition,
            hir::LoopIdError::UnresolvedLabel => Self::UnresolvedLabel,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ExprField<'hir>> for ExprField {
    fn from_hir(value: &'hir hir::ExprField<'hir>, tcx: TyCtxt<'hir>) -> Self {
        ExprField {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            expr: value.expr.hir_into(tcx),
            span: value.span.into(),
            is_shorthand: value.is_shorthand,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ArrayLen<'hir>> for ArrayLen {
    fn from_hir(value: &'hir hir::ArrayLen<'hir>, tcx: TyCtxt<'hir>) -> Self {
        match value {
            hir::ArrayLen::Infer(ia) => Self::Infer(ia.into()),
            hir::ArrayLen::Body(c) => Self::Body((*c).hir_into(tcx)),
        }
    }
}

impl From<&hir::InferArg> for InferArg {
    fn from(value: &hir::InferArg) -> Self {
        InferArg {
            hir_id: value.hir_id.into(),
            span: value.span.into(),
        }
    }
}

impl From<&hir::YieldSource> for YieldSource {
    fn from(value: &hir::YieldSource) -> Self {
        match value {
            hir::YieldSource::Await { expr } => Self::Await {
                expr: expr.map(|id| id.into()),
            },
            _ => Self::Yield,
        }
    }
}

impl From<hir::GenericParamSource> for GenericParamSource {
    fn from(value: hir::GenericParamSource) -> Self {
        match value {
            hir::GenericParamSource::Generics => Self::Generics,
            hir::GenericParamSource::Binder => Self::Binder,
        }
    }
}

impl<'hir, T, S> FromHir<'hir, &'hir [T]> for Vec<S>
where
    S: FromHir<'hir, &'hir T>,
    T: std::fmt::Debug,
{
    fn from_hir(value: &'hir [T], tcx: TyCtxt<'hir>) -> Self {
        value.iter().map(|i| i.hir_into(tcx)).collect()
    }
}

impl From<&hir::Lifetime> for Lifetime {
    fn from(value: &hir::Lifetime) -> Self {
        Lifetime {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            res: value.res.into(),
        }
    }
}

impl From<hir::LifetimeName> for LifetimeName {
    fn from(value: hir::LifetimeName) -> Self {
        match value {
            hir::LifetimeName::Param(ldid) => Self::Param(ldid.into()),
            hir::LifetimeName::ImplicitObjectLifetimeDefault => Self::ImplicitObjectLifetimeDefault,
            hir::LifetimeName::Error => Self::Error,
            hir::LifetimeName::Infer => Self::Infer,
            hir::LifetimeName::Static => Self::Static,
        }
    }
}

impl From<hir::GenericArgsParentheses> for GenericArgsParentheses {
    fn from(value: hir::GenericArgsParentheses) -> Self {
        match value {
            hir::GenericArgsParentheses::No => GenericArgsParentheses::No,
            hir::GenericArgsParentheses::ReturnTypeNotation => {
                GenericArgsParentheses::ReturnTypeNotation
            }
            hir::GenericArgsParentheses::ParenSugar => GenericArgsParentheses::ParenSugar,
        }
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::Ty<'tcx>> for Ty {
    fn from_hir(value: &rustc_middle::ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        match value.kind() {
            rustc_type_ir::TyKind::Bool => Self::Bool,
            rustc_type_ir::TyKind::Char => Self::Char,
            rustc_type_ir::TyKind::Int(int_ty) => Self::Int { ty: int_ty.into() },
            rustc_type_ir::TyKind::Uint(uint_ty) => Self::Uint { ty: uint_ty.into() },
            rustc_type_ir::TyKind::Float(float_ty) => Self::Float {
                ty: float_ty.into(),
            },
            rustc_type_ir::TyKind::Adt(def, args) => todo!("Adt"),
            rustc_type_ir::TyKind::Foreign(did) => Self::Foreign { def_id: did.into() },
            rustc_type_ir::TyKind::Str => Self::Str,
            rustc_type_ir::TyKind::Array(ty, len) => Self::Array {
                ty: Box::new(ty.hir_into(tcx)),
                len: Box::new(len.hir_into(tcx)),
            },
            rustc_type_ir::TyKind::Pat(ty, pat) => todo!("Pat"),
            rustc_type_ir::TyKind::Slice(ty) => todo!("Slice"),
            rustc_type_ir::TyKind::RawPtr(ty, mutability) => todo!("RawPtr"),
            rustc_type_ir::TyKind::Ref(_, ty, mutability) => Self::Ref {
                ty: Box::new(ty.hir_into(tcx)),
                r#mut: mut_to_bool(mutability),
            },
            rustc_type_ir::TyKind::FnDef(did, args) => todo!("FnDef"),
            rustc_type_ir::TyKind::FnPtr(binder, fn_header) => todo!("FnPtr"),
            rustc_type_ir::TyKind::Dynamic(binders, _, dyn_kind) => todo!("Dyn"),
            rustc_type_ir::TyKind::Closure(_, _) => todo!("Closure"),
            rustc_type_ir::TyKind::CoroutineClosure(_, _) => todo!("CoClosure"),
            rustc_type_ir::TyKind::Coroutine(_, _) => todo!("Co"),
            rustc_type_ir::TyKind::CoroutineWitness(_, _) => todo!("CoWit"),
            rustc_type_ir::TyKind::Never => Self::Never,
            rustc_type_ir::TyKind::Tuple(tys) => Self::Tuple {
                tys: tys.iter().map(|ty| (&ty).hir_into(tcx)).collect(),
            },
            rustc_type_ir::TyKind::Alias(alias_ty_kind, alias_ty) => Self::Alias {
                kind: alias_ty_kind.into(),
                ty: alias_ty.hir_into(tcx),
            },
            rustc_type_ir::TyKind::Param(p) => todo!("Param"),
            rustc_type_ir::TyKind::Bound(debruijn_index, ty) => todo!("Bound"),
            rustc_type_ir::TyKind::Placeholder(p) => Self::Placeholder {
                placeholder: p.hir_into(tcx),
            },
            rustc_type_ir::TyKind::Infer(infer_ty) => {
                todo!("Infer types should probably not be encountered at this point")
            }
            rustc_type_ir::TyKind::Error(_) => Self::Error,
        }
    }
}

#[inline]
fn mut_to_bool(m: &rustc_ast_ir::Mutability) -> bool {
    match m {
        rustc_ast::Mutability::Not => false,
        rustc_ast::Mutability::Mut => true,
    }
}

impl From<&rustc_middle::ty::IntTy> for IntTy {
    fn from(value: &rustc_middle::ty::IntTy) -> Self {
        match value {
            rustc_type_ir::IntTy::Isize => Self::Isize,
            rustc_type_ir::IntTy::I8 => Self::I8,
            rustc_type_ir::IntTy::I16 => Self::I16,
            rustc_type_ir::IntTy::I32 => Self::I32,
            rustc_type_ir::IntTy::I64 => Self::I64,
            rustc_type_ir::IntTy::I128 => Self::I128,
        }
    }
}

impl From<&rustc_middle::ty::UintTy> for UintTy {
    fn from(value: &rustc_middle::ty::UintTy) -> Self {
        match value {
            rustc_type_ir::UintTy::Usize => Self::Usize,
            rustc_type_ir::UintTy::U8 => Self::U8,
            rustc_type_ir::UintTy::U16 => Self::U16,
            rustc_type_ir::UintTy::U32 => Self::U32,
            rustc_type_ir::UintTy::U64 => Self::U64,
            rustc_type_ir::UintTy::U128 => Self::U128,
        }
    }
}

impl From<&rustc_middle::ty::FloatTy> for FloatTy {
    fn from(value: &rustc_middle::ty::FloatTy) -> Self {
        match value {
            rustc_type_ir::FloatTy::F16 => Self::F16,
            rustc_type_ir::FloatTy::F32 => Self::F32,
            rustc_type_ir::FloatTy::F64 => Self::F64,
            rustc_type_ir::FloatTy::F128 => Self::F128,
        }
    }
}

impl From<&rustc_middle::ty::AliasTyKind> for AliasTyKind {
    fn from(value: &rustc_middle::ty::AliasTyKind) -> Self {
        match value {
            rustc_type_ir::AliasTyKind::Projection => Self::Projection,
            rustc_type_ir::AliasTyKind::Inherent => Self::Inherent,
            rustc_type_ir::AliasTyKind::Opaque => Self::Opaque,
            rustc_type_ir::AliasTyKind::Weak => Self::Weak,
        }
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::AliasTy<'tcx>> for AliasTy {
    fn from_hir(value: &rustc_middle::ty::AliasTy<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            args: value
                .args
                .iter()
                .map(|i| i.unpack().hir_into(tcx))
                .collect(),
            def_id: (&value.def_id).into(),
        }
    }
}

impl<'tcx> FromHir<'tcx, rustc_middle::ty::GenericArgKind<'tcx>> for GenericTyArgKind {
    fn from_hir(value: rustc_middle::ty::GenericArgKind<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        match value {
            rustc_type_ir::GenericArgKind::Lifetime(_) => todo!("Lifetime"),
            rustc_type_ir::GenericArgKind::Type(ty) => Self::Type((&ty).hir_into(tcx)),
            rustc_type_ir::GenericArgKind::Const(c) => Self::Const((&c).hir_into(tcx)),
        }
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::Const<'tcx>> for Const {
    fn from_hir(value: &rustc_middle::ty::Const<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        match value.kind() {
            rustc_type_ir::ConstKind::Param(_) => todo!("Param"),
            rustc_type_ir::ConstKind::Infer(infer_const) => todo!("Infer"),
            rustc_type_ir::ConstKind::Bound(debruijn_index, _) => todo!("Bound"),
            rustc_type_ir::ConstKind::Placeholder(_) => todo!("PlaceHolder"),
            rustc_type_ir::ConstKind::Unevaluated(unevaluated_const) => todo!("Uneval"),
            rustc_type_ir::ConstKind::Value(_, _) => todo!("Val"),
            rustc_type_ir::ConstKind::Error(_) => Self::Error,
            rustc_type_ir::ConstKind::Expr(e) => todo!("Expr"),
        }
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::Placeholder<rustc_middle::ty::BoundTy>>
    for Placeholder<BoundTy>
{
    fn from_hir(
        value: &rustc_middle::ty::Placeholder<rustc_middle::ty::BoundTy>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Placeholder {
            universe: value.universe.into(),
            bound: (&value.bound).hir_into(tcx),
        }
    }
}

impl From<rustc_middle::ty::UniverseIndex> for UniverseIndex {
    fn from(value: rustc_middle::ty::UniverseIndex) -> Self {
        UniverseIndex(value.as_u32())
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::BoundTy> for BoundTy {
    fn from_hir(value: &rustc_middle::ty::BoundTy, tcx: TyCtxt<'tcx>) -> Self {
        BoundTy {
            var: value.var.into(),
            kind: (&value.kind).hir_into(tcx),
        }
    }
}

impl From<rustc_middle::ty::BoundVar> for BoundVar {
    fn from(value: rustc_middle::ty::BoundVar) -> Self {
        Self(value.as_u32())
    }
}

impl<'tcx> FromHir<'tcx, &rustc_middle::ty::BoundTyKind> for BoundTyKind {
    fn from_hir(value: &rustc_middle::ty::BoundTyKind, tcx: TyCtxt<'tcx>) -> Self {
        match value {
            rustc_middle::ty::BoundTyKind::Anon => Self::Anon,
            rustc_middle::ty::BoundTyKind::Param(def_id, symbol) => {
                Self::Param(def_id.into(), symbol.into())
            }
        }
    }
}
