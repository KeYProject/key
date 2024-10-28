use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Expr {
    pub hir_id: HirId,
    pub kind: Box<ExprKind>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ExprKind {
    ConstBlock(ConstBlock),
    Array(Vec<Expr>),
    Call(Expr, Vec<Expr>),
    MethodCall(PathSegment, Expr, Vec<Expr>, Span),
    Tup(Vec<Expr>),
    Binary(BinOp, Expr, Expr),
    Unary(UnOp, Expr),
    Lit(Lit),
    Cast(Expr, HirTy),
    Type(Expr, HirTy),
    DropTemps(Expr),
    Let(LetExpr),
    If(Expr, Expr, Option<Expr>),
    Loop(Block, Option<Label>, LoopSource, Span),
    Match(Expr, Vec<Arm>, MatchSource),
    Closure(Closure),
    Block(Block, Option<Label>),
    Assign(Expr, Expr, Span),
    AssignOp(BinOp, Expr, Expr),
    Field(Expr, Ident),
    Index(Expr, Expr, Span),
    Path(QPath),
    AddrOf(bool, bool, Expr),
    Break(Destination, Option<Expr>),
    Continue(Destination),
    Ret(Option<Expr>),
    Become(Expr),
    //InlineAsm(InlineAsm),
    OffsetOf(HirTy, Vec<Ident>),
    Struct(QPath, Vec<ExprField>, Option<Expr>),
    Repeat(Expr, ArrayLen),
    Yield(Expr, YieldSource),
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
pub enum LitKind {
    Str(Symbol, StrStyle),
    ByteStr(Vec<u8>, StrStyle),
    CStr(Vec<u8>, StrStyle),
    Byte(u8),
    Char(char),
    Int(u128, LitIntType),
    Float(Symbol, LitFloatType),
    Bool(bool),
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum StrStyle {
    Cooked,
    Raw(u8),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
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
pub enum BlockCheckMode {
    DefaultBlock,
    UnsafeBlock(UnsafeSource),
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
