use std::{collections::HashMap, num::NonZero};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum Ty {
    Bool,
    Char,
    Int {
        ty: IntTy,
    },
    Uint {
        ty: UintTy,
    },
    Float {
        ty: FloatTy,
    },
    Adt {
        def: AdtDef,
        args: Vec<GenericArg>,
    },
    Foreign {
        def_id: DefId,
    },
    Str,
    Array {
        ty: Box<Ty>,
        len: Box<Const>,
    },
    Pat {
        ty: Box<Ty>,
        pat: Box<Pattern>,
    },
    Slice {
        ty: Box<Ty>,
    },
    RawPtr {
        ty: Box<Ty>,
        r#mut: bool,
    },
    Ref {
        ty: Box<Ty>,
        r#mut: bool,
    },
    FnDef {
        def_id: DefId,
        args: Vec<GenericTyArgKind>,
    },
    FnPtr {
        binder: Binder<FnSigTys>,
        header: FnHeader,
    },
    Dynamic {
        binders: Vec<Binder<ExistentialPredicate>>,
        kind: DynKind,
    },
    Closure {
        def_id: DefId,
        args: Vec<GenericArg>,
    },
    CoroutineClosure {
        def_id: DefId,
        args: Vec<GenericArg>,
    },
    Coroutine {
        def_id: DefId,
        args: Vec<GenericArg>,
    },
    CoroutineWitness {
        def_id: DefId,
        args: Vec<GenericArg>,
    },
    Never,
    Tuple {
        tys: Vec<Ty>,
    },
    Alias {
        kind: AliasTyKind,
        ty: AliasTy,
    },
    Param {
        ty: ParamTy,
    },
    Bound {
        idx: DebruijnIndex,
        ty: BoundTy,
    },
    Placeholder {
        placeholder: Placeholder<BoundTy>,
    },
    Infer {
        infer: InferTy,
    },
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AdtDef {
    pub did: DefId,
    pub variants: HashMap<VariantIdx, VariantDef>,
    pub flags: AdtFlags,
    // pub repr: ReprOptions,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AdtFlags(u16);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct VariantIdx(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct VariantDef {
    pub def_id: DefId,
    pub ctor: Option<(CtorKind, DefId)>,
    pub name: Symbol,
    pub discr: VariantDiscr,
    pub fields: HashMap<FieldIdx, FieldDef>,
    pub tainted: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct FieldIdx(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CtorKind {
    Fn,
    Const,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum VariantDiscr {
    Explicit(DefId),
    Relative(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Const {
    Param(ParamConst),
    Infer(InferConst),
    Bound(DebruijnIndex, BoundVar),
    Placeholder(Placeholder<BoundVar>),
    Unevaluated(UnevaluatedConst),
    Value(Ty, ValTree),
    Error,
    Expr(ConstExpr),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ParamConst {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum InferConst {
    Var(ConstVid),
    EffectVar(EffectVid),
    Fresh(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConstVid(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConstExpr {
    pub kind: ConstExprKind,
    pub args: Vec<GenericTyArgKind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ConstExprKind {
    Binop(BinOpKind),
    UnOp(UnOp),
    FunctionCall,
    Cast(CastKind),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CastKind {
    As,
    Use,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EffectVid(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BoundVar(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct UnevaluatedConst {
    pub def: DefId,
    pub args: Vec<GenericTyArgKind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ValTree {
    Leaf(ScalarInt),
    Branch(Vec<ValTree>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ScalarInt {
    pub data: u128,
    pub size: NonZero<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum Pattern {
    Range {
        start: Option<Const>,
        end: Option<Const>,
        include_end: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Binder<T> {
    value: T,
    bound_vars: Vec<BoundVarKind>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BoundVarKind {
    Ty(BoundTyKind),
    Region(BoundRegionKind),
    Const,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BoundTyKind {
    Anon,
    Param(DefId, Symbol),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BoundRegionKind {
    BrAnon,
    BrNamed(DefId, Symbol),
    BrEnv,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FnSigTys {
    pub inputs_and_output: Vec<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ExistentialPredicate {
    Trait(ExistentialTraitRef),
    Projection(ExistentialProjection),
    AutoTrait(DefId),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExistentialTraitRef {
    pub def_id: DefId,
    pub args: GenericArgs,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExistentialProjection {
    pub def_id: DefId,
    pub args: Vec<GenericArg>,
    pub term: Term,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum DynKind {
    Dyn,
    DynStar,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum AliasTyKind {
    Projection,
    Inherent,
    Opaque,
    Weak,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct AliasTy {
    pub args: Vec<GenericTyArgKind>,
    pub def_id: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum GenericTyArgKind {
    //Lifetime(Region)
    Type(Ty),
    Const(Const),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ParamTy {
    pub index: u32,
    pub name: Symbol,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DebruijnIndex(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BoundTy {
    pub var: BoundVar,
    pub kind: BoundTyKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Placeholder<T> {
    pub universe: UniverseIndex,
    pub bound: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct UniverseIndex(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum InferTy {
    TyVar(TyVid),
    IntVar(IntVid),
    FloatVar(FloatVid),
    FreshTy(u32),
    FreshIntTy(u32),
    FreshFloatTy(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TyVid(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct IntVid(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct FloatVid(pub u32);
