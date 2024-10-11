use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stmt {
    pub hir_id: HirId,
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StmtKind {
    Let(LetStmt),
    Item(ItemId),
    Expr(Expr),
    Semi(Expr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStmt {
    pub pat: Pat,
    pub ty: Option<HirTy>,
    pub init: Option<Expr>,
    pub els: Option<Block>,
    pub hir_id: HirId,
    pub span: Span,
    pub source: LocalSource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LocalSource {
    Normal,
    AsyncFn,
    AwaitDesugar,
    AssignDesugar(Span),
}
