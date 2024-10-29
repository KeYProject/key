use serde::Serialize;

use expr::*;
use item::*;
use pat::*;
use stmt::*;
use ty::*;

pub mod conversion;
pub mod expr;
pub mod item;
pub mod pat;
pub mod stmt;
pub mod ty;
pub mod type_extract;
pub mod visit;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Crate {
    pub top_mod: Mod,
    pub types: Vec<(HirId, Ty)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Symbol(String);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BytePos(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct SyntaxContext(u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct LocalDefId {
    pub local_def_index: DefIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct DefIndex(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Span {
    pub lo: BytePos,
    pub hi: BytePos,
    //pub ctxt: SyntaxContext,
    pub parent: Option<LocalDefId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct OwnerId {
    pub def_id: LocalDefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HirTy {
    pub hir_id: HirId,
    pub kind: Box<HirTyKind>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub predicates: Vec<WherePredicate>,
    pub has_where_clause_predicates: bool,
    pub where_clause_span: Span,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum WherePredicate {
    Bound(WhereBoundPredicate),
    Region(WhereRegionPredicate),
    Eq(WhereEqPredicate),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WhereBoundPredicate {
    pub hir_id: HirId,
    pub span: Span,
    pub origin: PredicateOrigin,
    pub bound_generic_params: Vec<GenericParam>,
    pub bounded_ty: HirTy,
    pub bounds: GenericBounds,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum PredicateOrigin {
    WhereClause,
    GenericParam,
    ImplTrait,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WhereRegionPredicate {
    pub span: Span,
    pub in_where_clause: bool,
    pub lifetime: Lifetime,
    pub bounds: GenericBounds,
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WhereEqPredicate {
    pub span: Span,
    pub lhs_ty: HirTy,
    pub rhs_ty: HirTy,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum Defaultness {
    Default { has_value: bool },
    Final,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ImplItemId {
    pub owner_id: OwnerId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ItemId {
    pub owner_id: OwnerId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Path<R = Res> {
    pub span: Span,
    pub res: R,
    pub segments: Vec<PathSegment>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Def(pub DefKind, pub DefId);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum Res<Id = HirId> {
    Def {
        def: Def,
    },
    PrimTy {
        ty: PrimHirTy,
    },
    SelfTyParam {
        trait_: DefId,
    },
    SelfTyAlias {
        alias_to: DefId,
        forbid_generic: bool,
        is_trait_impl: bool,
    },
    SelfCtor(DefId),
    Local {
        id: Id,
    },
    ToolMod,
    NonMacroAttr(NonMacroAttrKind),
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct HirId {
    pub owner: OwnerId,
    pub local_id: ItemLocalId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct ItemLocalId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DefId {
    pub index: DefIndex,
    pub krate: CrateNum,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CrateNum(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
/// the second field is true iff it is a function ctor
pub struct Ctor(pub CtorOf, pub bool);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
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
    Ctor(Ctor),
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum NonMacroAttrKind {
    Builtin(Symbol),
    Tool,
    DeriveHelper,
    DeriveHelperCompat,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum PrimHirTy {
    Int { ty: IntTy },
    Uint { ty: UintTy },
    Float { ty: FloatTy },
    Str,
    Bool,
    Char,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CtorOf {
    Struct,
    Variant,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PathSegment {
    pub ident: Ident,
    pub hir_id: HirId,
    pub res: Res,
    pub args: Option<GenericArgs>,
    pub infer_args: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GenericArgs {
    pub args: Vec<GenericArg>,
    pub constraints: Vec<AssocItemConstraint>,
    pub parenthesized: GenericArgsParentheses,
    pub span_ext: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum GenericArg {
    Lifetime(Lifetime),
    Type(HirTy),
    Const(ConstArg),
    Infer(InferArg),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct InferArg {
    pub hir_id: HirId,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum GenericArgsParentheses {
    No,
    ReturnTypeNotation,
    ParenSugar,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AssocItemConstraint {
    pub hir_id: HirId,
    pub ident: Ident,
    pub gen_args: GenericArgs,
    pub kind: AssocItemConstraintKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum AssocItemConstraintKind {
    Equality { term: Term },
    Bound { bounds: Vec<GenericBound> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum GenericBound {
    Trait(PolyTraitRef),
    Outlives(Lifetime),
    Use(Vec<PreciseCapturingArg>, Span),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PolyTraitRef {
    pub bound_generic_params: Vec<GenericParam>,
    pub trait_ref: TraitRef,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum GenericParamSource {
    Generics,
    Binder,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ParamName {
    Plain(Ident),
    Fresh,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LifetimeParamKind {
    Explicit,
    Elided(MissingLifetimeKind),
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MissingLifetimeKind {
    Underscore,
    Ampersand,
    Comma,
    Brackets,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TraitRef {
    pub path: Path,
    pub hir_ref_id: HirId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum PreciseCapturingArg {
    Lifetime(Lifetime),
    Param(PreciseCapturingNonLifetimeArg),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Lifetime {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: LifetimeName,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PreciseCapturingNonLifetimeArg {
    pub hir_id: HirId,
    pub ident: Ident,
    pub res: Res,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LifetimeName {
    Param(LocalDefId),
    ImplicitObjectLifetimeDefault,
    Error,
    Infer,
    Static,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Term {
    Ty(HirTy),
    Const(ConstArg),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConstArg {
    pub hir_id: HirId,
    pub kind: ConstArgKind,
    pub is_desugared_from_effects: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ConstArgKind {
    Path(QPath),
    Anon(AnonConst),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AnonConst {
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub body: Body,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum QPath {
    Resolved { ty: Option<HirTy>, path: Path },
    TypeRelative { ty: HirTy, seg: PathSegment },
    LangItem { item: LangItem, span: Span },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BodyId {
    pub hir_id: HirId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LangItem {
    Sized,
    Unsize,
    StructuralPeq,
    Copy,
    Clone,
    CloneFn,
    Sync,
    DiscriminantKind,
    Discriminant,
    PointeeTrait,
    Metadata,
    DynMetadata,
    Freeze,
    FnPtrTrait,
    FnPtrAddr,
    Drop,
    Destruct,
    AsyncDrop,
    AsyncDestruct,
    AsyncDropInPlace,
    SurfaceAsyncDropInPlace,
    AsyncDropSurfaceDropInPlace,
    AsyncDropSlice,
    AsyncDropChain,
    AsyncDropNoop,
    AsyncDropDeferredDropInPlace,
    AsyncDropFuse,
    AsyncDropDefer,
    AsyncDropEither,
    CoerceUnsized,
    DispatchFromDyn,
    TransmuteOpts,
    TransmuteTrait,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Not,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    RemAssign,
    BitXorAssign,
    BitAndAssign,
    BitOrAssign,
    ShlAssign,
    ShrAssign,
    Index,
    IndexMut,
    UnsafeCell,
    VaList,
    Deref,
    DerefMut,
    DerefPure,
    DerefTarget,
    Receiver,
    Fn,
    FnMut,
    FnOnce,
    AsyncFn,
    AsyncFnMut,
    AsyncFnOnce,
    AsyncFnOnceOutput,
    CallOnceFuture,
    CallRefFuture,
    AsyncFnKindHelper,
    AsyncFnKindUpvars,
    FnOnceOutput,
    Iterator,
    FusedIterator,
    Future,
    FutureOutput,
    AsyncIterator,
    CoroutineState,
    Coroutine,
    CoroutineReturn,
    CoroutineYield,
    CoroutineResume,
    Unpin,
    Pin,
    OrderingEnum,
    PartialEq,
    PartialOrd,
    CVoid,
    Panic,
    PanicNounwind,
    PanicFmt,
    ConstPanicFmt,
    PanicBoundsCheck,
    PanicMisalignedPointerDereference,
    PanicInfo,
    PanicLocation,
    PanicImpl,
    PanicCannotUnwind,
    PanicInCleanup,
    PanicAddOverflow,
    PanicSubOverflow,
    PanicMulOverflow,
    PanicDivOverflow,
    PanicRemOverflow,
    PanicNegOverflow,
    PanicShrOverflow,
    PanicShlOverflow,
    PanicDivZero,
    PanicRemZero,
    PanicCoroutineResumed,
    PanicAsyncFnResumed,
    PanicAsyncGenFnResumed,
    PanicGenFnNone,
    PanicCoroutineResumedPanic,
    PanicAsyncFnResumedPanic,
    PanicAsyncGenFnResumedPanic,
    PanicGenFnNonePanic,
    BeginPanic,
    FormatAlignment,
    FormatArgument,
    FormatArguments,
    FormatCount,
    FormatPlaceholder,
    FormatUnsafeArg,
    ExchangeMalloc,
    DropInPlace,
    FallbackSurfaceDrop,
    AllocLayout,
    Start,
    EhPersonality,
    EhCatchTypeinfo,
    OwnedBox,
    GlobalAlloc,
    PtrUnique,
    PhantomData,
    ManuallyDrop,
    MaybeUninit,
    AlignOffset,
    Termination,
    Try,
    Tuple,
    SliceLen,
    TryTraitFromResidual,
    TryTraitFromOutput,
    TryTraitBranch,
    TryTraitFromYeet,
    PointerLike,
    ConstParamTy,
    UnsizedConstParamTy,
    Poll,
    PollReady,
    PollPending,
    AsyncGenReady,
    AsyncGenPending,
    AsyncGenFinished,
    ResumeTy,
    GetContext,
    Context,
    FuturePoll,
    AsyncIteratorPollNext,
    IntoAsyncIterIntoIter,
    Option,
    OptionSome,
    OptionNone,
    ResultOk,
    ResultErr,
    ControlFlowContinue,
    ControlFlowBreak,
    IntoFutureIntoFuture,
    IntoIterIntoIter,
    IteratorNext,
    PinNewUnchecked,
    RangeFrom,
    RangeFull,
    RangeInclusiveStruct,
    RangeInclusiveNew,
    Range,
    RangeToInclusive,
    RangeTo,
    String,
    CStr,
    EffectsRuntime,
    EffectsNoRuntime,
    EffectsMaybe,
    EffectsIntersection,
    EffectsIntersectionOutput,
    EffectsCompat,
    EffectsTyCompat,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}
