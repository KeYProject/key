use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Expr {
    pub hir_id: HirId,
    pub kind: Box<ExprKind>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum ExprKind {
    ConstBlock {
        block: ConstBlock,
    },
    Array {
        exprs: Vec<Expr>,
    },
    Call {
        callee: Expr,
        args: Vec<Expr>,
    },
    MethodCall {
        segment: PathSegment,
        callee: Expr,
        args: Vec<Expr>,
        span: Span,
    },
    Tup {
        exprs: Vec<Expr>,
    },
    Binary {
        op: BinOp,
        left: Expr,
        right: Expr,
    },
    Unary {
        op: UnOp,
        expr: Expr,
    },
    Lit {
        lit: Lit,
    },
    Cast {
        expr: Expr,
        ty: HirTy,
    },
    Type {
        expr: Expr,
        ty: HirTy,
    },
    DropTemps {
        expr: Expr,
    },
    Let {
        r#let: LetExpr,
    },
    If {
        cond: Expr,
        then: Expr,
        els: Option<Expr>,
    },
    Loop {
        block: Block,
        label: Option<Label>,
        src: LoopSource,
        span: Span,
    },
    Match {
        expr: Expr,
        arms: Vec<Arm>,
        src: MatchSource,
    },
    Closure {
        closure: Closure,
    },
    Block {
        block: Block,
        label: Option<Label>,
    },
    Assign {
        left: Expr,
        right: Expr,
        span: Span,
    },
    AssignOp {
        op: BinOp,
        left: Expr,
        right: Expr,
    },
    Field {
        expr: Expr,
        field: Ident,
    },
    Index {
        base: Expr,
        idx: Expr,
        span: Span,
    },
    Path {
        path: QPath,
    },
    AddrOf {
        raw: bool,
        r#mut: bool,
        expr: Expr,
    },
    Break {
        dest: Destination,
        expr: Option<Expr>,
    },
    Continue {
        dest: Destination,
    },
    Ret {
        expr: Option<Expr>,
    },
    Become {
        expr: Expr,
    },
    //InlineAsm(InlineAsm),
    OffsetOf {
        ty: HirTy,
        idents: Vec<Ident>,
    },
    Struct {
        path: QPath,
        fields: Vec<ExprField>,
        rest: Option<Expr>,
    },
    Repeat {
        expr: Expr,
        len: ArrayLen,
    },
    Yield {
        expr: Expr,
        src: YieldSource,
    },
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConstBlock {
    pub hir_id: HirId,
    pub def_id: LocalDefId,
    pub body: Body,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum UnOp {
    Deref,
    Not,
    Neg,
}

pub type Lit = Spanned<LitKind>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum LitKind {
    Str { symbol: Symbol, style: StrStyle },
    ByteStr { bytes: Vec<u8>, style: StrStyle },
    CStr { bytes: Vec<u8>, style: StrStyle },
    Byte { byte: u8 },
    Char { char: char },
    Int { value: u128, ty: LitIntType },
    Float { symbol: Symbol, ty: LitFloatType },
    Bool { value: bool },
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum StrStyle {
    Cooked,
    Raw(u8),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum LitIntType {
    Signed { ty: IntTy },
    Unsigned { ty: UintTy },
    Unsuffixed,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LitFloatType {
    Suffixed(FloatTy),
    Unsuffixed,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LetExpr {
    pub span: Span,
    pub pat: Pat,
    pub ty: Option<HirTy>,
    pub init: Expr,
    pub recovered: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LoopSource {
    Loop,
    While,
    ForLoop,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Arm {
    pub hir_id: HirId,
    pub span: Span,
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum MatchSource {
    Normal,
    Postfix,
    ForLoopDesugar,
    TryDesugar(HirId),
    AwaitDesugar,
    FormatArgs,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Closure {
    pub def_id: LocalDefId,
    pub binder: ClosureBinder,
    pub constness: bool,
    pub capture_clause: CaptureBy,
    pub bound_generic_params: Vec<GenericParam>,
    pub fn_decl: FnDecl,
    pub body: Body,
    pub fn_decl_span: Span,
    pub fn_arg_span: Option<Span>,
    //pub kind: ClosureKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ClosureBinder {
    Default,
    For { span: Span },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum CaptureBy {
    Value { move_kw: Span },
    Ref,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub expr: Option<Expr>,
    pub hir_id: HirId,
    pub rules: BlockCheckMode,
    pub span: Span,
    pub targeted_by_break: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum BlockCheckMode {
    DefaultBlock,
    UnsafeBlock { src: UnsafeSource },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum UnsafeSource {
    CompilerGenerated,
    UserProvided,
}

pub type BinOp = Spanned<BinOpKind>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Destination {
    pub label: Option<Label>,
    pub target_id: Result<HirId, LoopIdError>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Label {
    pub ident: Ident,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LoopIdError {
    OutsideLoopScope,
    UnlabeledCfInWhileCondition,
    UnresolvedLabel,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ExprField {
    pub hir_id: HirId,
    pub ident: Ident,
    pub expr: Expr,
    pub span: Span,
    pub is_shorthand: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum YieldSource {
    Await { expr: Option<HirId> },
    Yield,
}
