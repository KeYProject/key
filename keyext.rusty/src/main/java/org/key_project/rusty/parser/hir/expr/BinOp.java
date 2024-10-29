package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.Span;

public record BinOp(BinOpKind node, Span span) {
}
