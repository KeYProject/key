use rustc_hir as hir;
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_span::{
    def_id::{DefIndex as HirDefIndex, LocalDefId as HirLocalDefId},
    symbol::Ident as HirIdent,
    BytePos as HirBytePos, Span as HirSpan, Symbol as HirSymbol,
};

use super::*;

pub fn convert<'tcx>(tcx: &'tcx TyCtxt<'tcx>) -> Crate {
    let hir = tcx.hir();
    let m = hir.root_module();
    Crate {
        top_mod: m.hir_into(hir),
    }
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
    fn from_hir(value: T, hir: Map<'hir>) -> Self;
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
    fn hir_into(self, hir: Map<'hir>) -> T;
}

impl<'hir, T, U> HirInto<'hir, U> for T
where
    U: FromHir<'hir, T>,
{
    fn hir_into(self, hir: Map<'hir>) -> U {
        U::from_hir(self, hir)
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Mod<'hir>> for Mod {
    fn from_hir(value: &'hir hir::Mod<'hir>, hir: Map<'hir>) -> Self {
        Mod {
            spans: value.spans.into(),
            items: value
                .item_ids
                .iter()
                .map(|id| hir.item(*id).hir_into(hir))
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
    fn from_hir(value: &'hir hir::Item<'hir>, hir: Map<'hir>) -> Self {
        Item {
            ident: value.ident.into(),
            owner_id: value.owner_id.into(),
            kind: (&value.kind).hir_into(hir),
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
        Symbol(value.as_u32())
    }
}

impl From<&HirSymbol> for Symbol {
    fn from(value: &HirSymbol) -> Self {
        Symbol(value.as_u32())
    }
}

impl From<hir::OwnerId> for OwnerId {
    fn from(value: hir::OwnerId) -> Self {
        OwnerId {
            def_id: value.def_id.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ItemKind<'hir>> for ItemKind {
    fn from_hir(value: &'hir hir::ItemKind<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::ItemKind::ExternCrate(symbol) => ItemKind::ExternCrate(symbol.map(|s| s.into())),
            hir::ItemKind::Use(path, use_kind) => ItemKind::Use(
                Path {
                    span: path.span.into(),
                    res: path.res.as_slice().hir_into(hir),
                    segments: path.segments.iter().map(|s| s.hir_into(hir)).collect(),
                },
                use_kind.into(),
            ),
            hir::ItemKind::Static(hir_ty, _, body) => todo!(),
            hir::ItemKind::Const(hir_ty, generics, body) => todo!(),
            hir::ItemKind::Fn(fn_sig, generics, body) => todo!(),
            hir::ItemKind::Mod(_) => todo!(),
            hir::ItemKind::TyAlias(hir_ty, generics) => todo!(),
            hir::ItemKind::Enum(enum_def, generics) => todo!(),
            hir::ItemKind::Struct(variant_data, generics) => todo!(),
            hir::ItemKind::Union(variant_data, generics) => todo!(),
            hir::ItemKind::Trait(_, _, generics, vec, vec1) => todo!(),
            hir::ItemKind::TraitAlias(generics, vec) => todo!(),
            hir::ItemKind::Impl(_) => todo!(),
            hir::ItemKind::Macro(..) => todo!(),
            hir::ItemKind::ForeignMod { .. } => todo!(),
            hir::ItemKind::GlobalAsm(..) => todo!(),
        }
    }
}

impl<'hir, R, T> FromHir<'hir, &'hir hir::Path<'hir, R>> for Path<T>
where
    T: FromHir<'hir, &'hir R>,
{
    fn from_hir(value: &'hir hir::Path<'hir, R>, hir: Map<'hir>) -> Self {
        Path {
            span: value.span.into(),
            res: (&value.res).hir_into(hir),
            segments: value.segments.iter().map(|s| s.hir_into(hir)).collect(),
        }
    }
}

/* impl<'hir> FromHir<'hir, &'hir [hir::def::Res]> for Vec<Res> {
    fn from_hir(value: &'hir [hir::def::Res], hir: Map<'hir>) -> Self {
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
    fn from_hir(value: &'hir hir::PathSegment<'hir>, hir: Map<'hir>) -> Self {
        PathSegment {
            ident: value.ident.into(),
            hir_id: value.hir_id.into(),
            res: value.res.into(),
            args: value.args.map(|a| a.hir_into(hir)),
            infer_args: value.infer_args,
        }
    }
}

impl From<hir::HirId> for HirId {
    fn from(value: hir::HirId) -> Self {
        todo!()
    }
}

impl From<&hir::HirId> for HirId {
    fn from(value: &hir::HirId) -> Self {
        todo!()
    }
}

impl From<hir::def::Res> for Res {
    fn from(value: hir::def::Res) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericArgs<'hir>> for GenericArgs {
    fn from_hir(value: &'hir hir::GenericArgs<'hir>, hir: Map<'hir>) -> Self {
        GenericArgs {
            args: value.args.hir_into(hir),
            constraints: value.constraints.hir_into(hir),
            parenthesized: value.parenthesized.into(),
            span_ext: value.span_ext.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericArg<'hir>> for GenericArg {
    fn from_hir(value: &'hir hir::GenericArg<'hir>, hir: Map<'hir>) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::AssocItemConstraint<'hir>> for AssocItemConstraint {
    fn from_hir(value: &'hir hir::AssocItemConstraint<'hir>, hir: Map<'hir>) -> Self {
        AssocItemConstraint {
            hir_id: value.hir_id.into(),
            ident: value.ident.into(),
            gen_args: value.gen_args.hir_into(hir),
            kind: (&value.kind).hir_into(hir),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::AssocItemConstraintKind<'hir>> for AssocItemConstraintKind {
    fn from_hir(value: &'hir hir::AssocItemConstraintKind<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::AssocItemConstraintKind::Equality { term } => AssocItemConstraintKind::Equality {
                term: term.hir_into(hir),
            },
            hir::AssocItemConstraintKind::Bound { bounds } => AssocItemConstraintKind::Bound {
                bounds: (*bounds).hir_into(hir),
            },
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Term<'hir>> for Term {
    fn from_hir(value: &'hir hir::Term<'hir>, hir: Map<'hir>) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericBound<'hir>> for GenericBound {
    fn from_hir(value: &'hir hir::GenericBound<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::GenericBound::Trait(r, m) => GenericBound::Trait(r.hir_into(hir), m.into()),
            hir::GenericBound::Outlives(l) => GenericBound::Outlives((*l).into()),
            hir::GenericBound::Use(..) => todo!(),
        }
    }
}

impl From<&hir::TraitBoundModifier> for TraitBoundModifier {
    fn from(value: &hir::TraitBoundModifier) -> Self {
        match value {
            hir::TraitBoundModifier::None => Self::None,
            hir::TraitBoundModifier::Negative => Self::Negative,
            hir::TraitBoundModifier::Maybe => Self::Maybe,
            hir::TraitBoundModifier::Const => Self::Const,
            hir::TraitBoundModifier::MaybeConst => Self::MaybeConst,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::PolyTraitRef<'hir>> for PolyTraitRef {
    fn from_hir(value: &'hir hir::PolyTraitRef<'hir>, hir: Map<'hir>) -> Self {
        PolyTraitRef {
            bound_generic_params: value.bound_generic_params.hir_into(hir),
            trait_ref: (&value.trait_ref).hir_into(hir),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::TraitRef<'hir>> for TraitRef {
    fn from_hir(value: &'hir hir::TraitRef<'hir>, hir: Map<'hir>) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericParam<'hir>> for GenericParam {
    fn from_hir(value: &'hir hir::GenericParam<'hir>, hir: Map<'hir>) -> Self {
        GenericParam {
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            name: value.name.into(),
            span: value.span.into(),
            pure_wrt_drop: value.pure_wrt_drop,
            kind: (&value.kind).hir_into(hir),
            colon_span: value.colon_span.map(Into::into),
            source: value.source.into(),
        }
    }
}

impl From<hir::ParamName> for ParamName {
    fn from(value: hir::ParamName) -> Self {
        match value {
            hir::ParamName::Plain(..) => todo!(),
            hir::ParamName::Fresh => todo!(),
            hir::ParamName::Error => todo!(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::GenericParamKind<'hir>> for GenericParamKind {
    fn from_hir(value: &'hir hir::GenericParamKind<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::GenericParamKind::Lifetime { kind } => Self::Lifetime { kind: kind.into() },
            hir::GenericParamKind::Type { default, synthetic } => Self::Type {
                default: default.map(|ty| ty.hir_into(hir)),
                synthetic: *synthetic,
            },
            hir::GenericParamKind::Const {
                ty,
                default,
                is_host_effect,
                synthetic,
            } => Self::Const {
                ty: (*ty).hir_into(hir),
                default: default.map(|d| d.hir_into(hir)),
                is_host_effect: *is_host_effect,
                synthetic: *synthetic,
            },
        }
    }
}

impl From<&hir::LifetimeParamKind> for LifetimeParamKind {
    fn from(value: &hir::LifetimeParamKind) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ConstArg<'hir>> for ConstArg {
    fn from_hir(value: &'hir hir::ConstArg<'hir>, hir: Map<'hir>) -> Self {
        ConstArg {
            hir_id: value.hir_id.into(),
            kind: (&value.kind).hir_into(hir),
            is_desugared_from_effects: value.is_desugared_from_effects,
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::ConstArgKind<'hir>> for ConstArgKind {
    fn from_hir(value: &'hir hir::ConstArgKind<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::ConstArgKind::Path(qpath) => Self::Path(qpath.hir_into(hir)),
            hir::ConstArgKind::Anon(anon_const) => Self::Anon((*anon_const).hir_into(hir)),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::QPath<'hir>> for QPath {
    fn from_hir(value: &'hir hir::QPath<'hir>, hir: Map<'hir>) -> Self {
        match value {
            hir::QPath::Resolved(ty, p) => {
                Self::Resolved(ty.map(|t| t.hir_into(hir)), (*p).hir_into(hir))
            }
            hir::QPath::TypeRelative(..) => todo!(),
            hir::QPath::LangItem(..) => todo!(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Ty<'hir>> for HirTy {
    fn from_hir(value: &'hir hir::Ty<'hir>, hir: Map<'hir>) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::def::Res> for Res {
    fn from_hir(value: &'hir hir::def::Res, hir: Map<'hir>) -> Self {
        match value {
            hir::def::Res::Def(kind, id) => Self::Def(kind.into(), id.into()),
            hir::def::Res::PrimTy(ty) => Self::PrimTy(ty.into()),
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
            hir::def::Res::Local(id) => Self::Local(id.into()),
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
            hir::def::DefKind::Ctor(of, hir::def::CtorKind::Fn) => Self::Ctor(of.into(), true),
            hir::def::DefKind::Ctor(of, hir::def::CtorKind::Const) => Self::Ctor(of.into(), false),
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
            hir::PrimTy::Int(i) => Self::Int(i.into()),
            hir::PrimTy::Uint(i) => Self::Uint(i.into()),
            hir::PrimTy::Float(f) => Self::Float(f.into()),
            hir::PrimTy::Str => Self::Str,
            hir::PrimTy::Bool => Self::Bool,
            hir::PrimTy::Char => Self::Char,
        }
    }
}

impl From<&rustc_ast::IntTy> for IntHirTy {
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

impl From<&rustc_ast::UintTy> for UintHirTy {
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

impl From<&rustc_ast::FloatTy> for FloatHirTy {
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
    fn from_hir(value: &'hir hir::AnonConst, hir: Map<'hir>) -> Self {
        AnonConst {
            hir_id: value.hir_id.into(),
            def_id: value.def_id.into(),
            body: hir.body(value.body).hir_into(hir),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Body<'hir>> for Body {
    fn from_hir(value: &'hir hir::Body<'hir>, hir: Map<'hir>) -> Self {
        Body {
            params: value.params.hir_into(hir),
            value: value.value.hir_into(hir),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Param<'hir>> for Param {
    fn from_hir(value: &'hir hir::Param<'hir>, hir: Map<'hir>) -> Self {
        Param {
            hir_id: value.hir_id.into(),
            pat: value.pat.hir_into(hir),
            ty_span: value.ty_span.into(),
            span: value.span.into(),
        }
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Pat<'hir>> for Pat {
    fn from_hir(value: &'hir hir::Pat<'hir>, hir: Map<'hir>) -> Self {
        todo!()
    }
}

impl<'hir> FromHir<'hir, &'hir hir::Expr<'hir>> for Expr {
    fn from_hir(value: &'hir hir::Expr<'hir>, hir: Map<'hir>) -> Self {
        todo!()
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
{
    fn from_hir(value: &'hir [T], hir: Map<'hir>) -> Self {
        value.hir_into(hir)
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
