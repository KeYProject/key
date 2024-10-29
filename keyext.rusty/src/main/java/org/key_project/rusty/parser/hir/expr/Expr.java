package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record Expr(HirId hirId, ExprKind kind, Span span) {
}
