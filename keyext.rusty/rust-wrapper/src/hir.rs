use expr::*;
use item::*;
use pat::*;
use stmt::*;

pub mod conversion;
pub mod expr;
pub mod item;
pub mod pat;
pub mod stmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Crate {
    pub top_mod: Mod,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BytePos(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxContext(u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDefId {
    pub local_def_index: DefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefIndex(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub lo: BytePos,
    pub hi: BytePos,
    //pub ctxt: SyntaxContext,
    pub parent: Option<LocalDefId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnerId {
    pub def_id: LocalDefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirTy {
    pub hir_id: HirId,
    pub kind: Box<HirTyKind>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub predicates: Vec<WherePredicate>,
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WherePredicate {
    BoundPredicate(WhereBoundPredicate),
    RegionPredicate(WhereRegionPredicate),
    EqPredicate(WhereEqPredicate),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhereBoundPredicate {
    pub hir_id: HirId,
    pub span: Span,
    pub origin: PredicateOrigin,
    pub bound_generic_params: Vec<GenericParam>,
    pub bounded_ty: HirTy,
    pub bounds: GenericBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhereRegionPredicate {
    pub span: Span,
    pub in_where_clause: bool,
    pub lifetime: Lifetime,
    pub bounds: GenericBounds,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WhereEqPredicate {
    pub span: Span,
    pub lhs_ty: HirTy,
    pub rhs_ty: HirTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Defaultness {
    Default { has_value: bool },
    Final,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplItemId {
    pub owner_id: OwnerId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItemId {
    pub owner_id: OwnerId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Path<R = Res> {
    pub span: Span,
    pub res: R,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Res<Id = HirId> {
    Def(DefKind, DefId),
    PrimTy(PrimHirTy),
    SelfTyParam {
        trait_: DefId,
    },
    SelfTyAlias {
        alias_to: DefId,
        forbid_generic: bool,
        is_trait_impl: bool,
    },
    SelfCtor(DefId),
    Local(Id),
    ToolMod,
    NonMacroAttr(NonMacroAttrKind),
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirId {
    pub owner: OwnerId,
    pub local_id: ItemLocalId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ItemLocalId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefId {
    pub index: DefIndex,
    pub krate: CrateNum,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrateNum(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefKind {
    Mod,
    Struct,
    Union,
    Enum,
    Variant,
    Trait,
    TyAlias,
    ForeignTy,
    TraitAlias,
    AssocTy,
    TyParam,
    Fn,
    Const,
    ConstParam,
    Static {
        safety: bool,
        mutability: bool,
        nested: bool,
    },
    /// the second field is true iff it is a function ctor
    Ctor(CtorOf, bool),
    AssocFn,
    AssocConst,
    Macro(MacroKind),
    ExternCrate,
    Use,
    ForeignMod,
    AnonConst,
    InlineConst,
    OpaqueTy,
    Field,
    LifetimeParam,
    GlobalAsm,
    Impl {
        of_trait: bool,
    },
    Closure,
    SyntheticCoroutineBody,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonMacroAttrKind {
    Builtin(Symbol),
    Tool,
    DeriveHelper,
    DeriveHelperCompat,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimHirTy {
    Int(IntHirTy),
    Uint(UintHirTy),
    Float(FloatHirTy),
    Str,
    Bool,
    Char,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntHirTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UintHirTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FloatHirTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtorOf {
    Struct,
    Variant,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathSegment {
    pub ident: Ident,
    pub hir_id: HirId,
    pub res: Res,
    pub args: Option<GenericArgs>,
    pub infer_args: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericArgs {
    pub args: Vec<GenericArg>,
    pub constraints: Vec<AssocItemConstraint>,
    pub parenthesized: GenericArgsParentheses,
    pub span_ext: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericArg {
    Lifetime(Lifetime),
    Type(HirTy),
    Const(ConstArg),
    Infer(InferArg),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferArg {
    pub hir_id: HirId,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericArgsParentheses {
    No,
    ReturnTypeNotation,
    ParenSugar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssocItemConstraint {
    pub hir_id: HirId,
    pub ident: Ident,
    pub gen_args: GenericArgs,
    pub kind: AssocItemConstraintKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssocItemConstraintKind {
    Equality { term: Term },
    Bound { bounds: Vec<GenericBound> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericBound {
    Trait(PolyTraitRef, TraitBoundModifier),
    Outlives(Lifetime),
    Use(Vec<PreciseCapturingArg>, Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitBoundModifier {
    None,
    Negative,
    Maybe,
    Const,
    MaybeConst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyTraitRef {
    pub bound_generic_params: Vec<GenericParam>,
    pub trait_ref: TraitRef,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericParam {
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub name: ParamName,
    pub span: Span,
    pub pure_wrt_drop: bool,
    pub kind: GenericParamKind,
    pub colon_span: Option<Span>,
    pub source: GenericParamSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericParamSource {
    Generics,
    Binder,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamName {
    Plain(Ident),
    Fresh,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericParamKind {
    Lifetime {
        kind: LifetimeParamKind,
    },
    Type {
        default: Option<HirTy>,
        synthetic: bool,
    },
    Const {
        ty: HirTy,
        default: Option<ConstArg>,
        is_host_effect: bool,
        synthetic: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LifetimeParamKind {
    Explicit,
    Elided(MissingLifetimeKind),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MissingLifetimeKind {
    Underscore,
    Ampersand,
    Comma,
    Brackets,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitRef {
    pub path: Path,
    pub hir_ref_id: HirId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreciseCapturingArg {
    Lifetime(Lifetime),
    Param(PreciseCapturingNonLifetimeArg),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lifetime {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: LifetimeName,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreciseCapturingNonLifetimeArg {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: Res,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LifetimeName {
    Param(LocalDefId),
    ImplicitObjectLifetimeDefault,
    Error,
    Infer,
    Static,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Ty(HirTy),
    Const(ConstArg),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstArg {
    pub hir_id: HirId,
    pub kind: ConstArgKind,
    pub is_desugared_from_effects: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstArgKind {
    Path(QPath),
    Anon(AnonConst),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnonConst {
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub body: Body,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QPath {
    Resolved(Option<HirTy>, Path),
    TypeRelative(HirTy, PathSegment),
    LangItem(LangItem, Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyId {
    pub hir_id: HirId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LangItem {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
