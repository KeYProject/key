use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Pat {
    pub hir_id: HirId,
    pub kind: Box<PatKind>,
    pub span: Span,
    pub default_binding_modes: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum PatKind {
    Wild,
    Binding {
        mode: BindingMode,
        hir_id: HirId,
        ident: Ident,
        pat: Option<Pat>,
    },
    Struct {
        path: QPath,
        fields: Vec<PatField>,
        rest: bool,
    },
    TupleStruct {
        path: QPath,
        pats: Vec<Pat>,
        dot_dot_pos: DotDotPos,
    },
    Or {
        pats: Vec<Pat>,
    },
    Never,
    Path {
        path: QPath,
    },
    Tuple {
        pats: Vec<Pat>,
        dot_dot_pos: DotDotPos,
    },
    Box {
        pat: Pat,
    },
    Deref {
        pat: Pat,
    },
    Ref {
        pat: Pat,
        r#mut: bool,
    },
    Lit {
        expr: Expr,
    },
    Range {
        lhs: Option<Expr>,
        rhs: Option<Expr>,
        inclusive: bool,
    },
    Slice {
        start: Vec<Pat>,
        mid: Option<Pat>,
        rest: Vec<Pat>,
    },
    Err,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct BindingMode {
    pub by_ref: ByRef,
    pub r#mut: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "serde_tag")]
pub enum ByRef {
    Yes { r#mut: bool },
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
