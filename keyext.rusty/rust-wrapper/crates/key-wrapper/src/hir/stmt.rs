use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Stmt {
    pub hir_id: HirId,
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum StmtKind {
    Let { r#let: LetStmt },
    Item { item: Item },
    Expr { expr: Expr },
    Semi { expr: Expr },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct LetStmt {
    pub pat: Pat,
    pub ty: Option<HirTy>,
    pub init: Option<Expr>,
    pub els: Option<Block>,
    pub hir_id: HirId,
    pub span: Span,
    pub source: LocalSource,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum LocalSource {
    Normal,
    AsyncFn,
    AwaitDesugar,
    AssignDesugar { span: Span },
}
