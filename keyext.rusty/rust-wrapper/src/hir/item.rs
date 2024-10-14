use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    pub ident: Ident,
    pub owner_id: OwnerId,
    pub kind: ItemKind,
    pub span: Span,
    pub vis_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemKind {
    ExternCrate(Option<Symbol>),
    Use(UsePath, UseKind),
    Static(HirTy, bool, Body),
    Const(HirTy, Generics, Body),
    Fn(FnSig, Generics, Body),
    //Macro(MacroDef, MacroKind),
    Mod(Mod),
    /* ForeignMod {
        abi: Abi,
        items: [ForeignItemRef],
    }, */
    //GlobalAsm(InlineAsm),
    TyAlias(HirTy, Generics),
    //OpaqueTy(OpaqueTy),
    Enum(EnumDef, Generics),
    Struct(VariantData, Generics),
    Union(VariantData, Generics),
    Trait(bool, bool, Generics, GenericBounds, Vec<TraitItemRef>),
    TraitAlias(Generics, GenericBounds),
    Impl(Impl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Body {
    pub params: Vec<Param>,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub hir_id: HirId,
    pub pat: Pat,
    pub ty_span: Span,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig {
    pub header: FnHeader,
    pub decl: FnDecl,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnHeader {
    pub safety: bool,
    pub constness: bool,
    pub asyncness: bool,
    //pub abi: Abi,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mod {
    pub spans: ModSpans,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModSpans {
    pub inner_span: Span,
    pub inject_use_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDef {
    pub variants: Vec<Variant>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub data: VariantData,
    pub disr_expr: Option<AnonConst>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VariantData {
    Struct {
        fields: Vec<FieldDef>,
        recovered: bool,
    },
    Tuple(Vec<FieldDef>, HirId, LocalDefId),
    Unit(HirId, LocalDefId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDef {
    pub span: Span,
    pub vis_span: Span,
    pub ident: Ident,
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub ty: HirTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitItemRef {
    pub id: TraitItemId,
    pub ident: Ident,
    pub kind: AssocItemKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitItemId {
    pub owner_id: OwnerId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Impl {
    pub constness: bool,
    pub safety: bool,
    pub polarity: ImplPolarity,
    pub defaultness: Defaultness,
    pub defaultness_span: Option<Span>,
    pub generics: Generics,
    pub of_trait: Option<TraitRef>,
    pub self_ty: HirTy,
    pub items: Vec<ImplItemRef>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplPolarity {
    Positive,
    Negative(Span),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplItemRef {
    pub id: ImplItemId,
    pub ident: Ident,
    pub kind: AssocItemKind,
    pub span: Span,
    pub trait_item_def_id: Option<DefId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HirTyKind {
    InferDelegation(DefId, InferDelegationKind),
    Slice(HirTy),
    Array(HirTy, ArrayLen),
    Ptr(MutHirTy),
    Ref(Lifetime, MutHirTy),
    BareFn(BareFnHirTy),
    Never,
    Tup(Vec<HirTy>),
    AnonAdt(Item),
    Path(QPath),
    // OpaqueDef(Item, Vec<GenericArg>, bool),
    TraitObject(
        Vec<(PolyTraitRef, TraitBoundModifier)>,
        Lifetime,
        TraitObjectSyntax,
    ),
    Typeof(AnonConst),
    Infer,
    Err,
    Pat(HirTy, Pat),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssocItemKind {
    Const,
    Fn { has_self: bool },
    Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitObjectSyntax {
    Dyn,
    DynStar,
    None,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InferDelegationKind {
    Input(usize),
    Output,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArrayLen {
    Infer(InferArg),
    Body(ConstArg),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MutHirTy {
    pub ty: HirTy,
    pub mutbl: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BareFnHirTy {
    pub safety: bool,
    //pub abi: Abi,
    pub generic_params: Vec<GenericParam>,
    pub decl: FnDecl,
    pub param_names: Vec<Ident>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnDecl {
    pub inputs: Vec<HirTy>,
    pub output: FnRetTy,
    pub c_variadic: bool,
    pub implicit_self: ImplicitSelfKind,
    pub lifetime_elision_allowed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FnRetTy {
    DefaultReturn(Span),
    Return(HirTy),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplicitSelfKind {
    Imm,
    Mut,
    RefImm,
    RefMut,
    None,
}

pub type UsePath = Path<Vec<Res>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseKind {
    Single,
    Glob,
    ListStem,
}
