use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Pat {
    pub hir_id: HirId,
    pub kind: Box<PatKind>,
    pub span: Span,
    pub default_binding_modes: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum PatKind {
    Wild,
    Binding(BindingMode, HirId, Ident, Option<Pat>),
    Struct(QPath, Vec<PatField>, bool),
    TupleStruct(QPath, Vec<Pat>, DotDotPos),
    Or(Vec<Pat>),
    Never,
    Path(QPath),
    Tuple(Vec<Pat>, DotDotPos),
    Box(Pat),
    Deref(Pat),
    Ref(Pat, bool),
    Lit(Expr),
    Range(Option<Expr>, Option<Expr>, bool),
    Slice(Vec<Pat>, Option<Pat>, Vec<Pat>),
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BindingMode(pub ByRef, pub bool);

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum ByRef {
    Yes(bool),
    No,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct PatField {
    pub hir_id: HirId,
    pub ident: Ident,
    pub pat: Pat,
    pub is_shorthand: bool,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DotDotPos(pub u32);
