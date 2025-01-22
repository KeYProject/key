package org.key_project.rusty.speclang.spec;

import org.key_project.rusty.parser.hir.expr.BinOp;
import org.key_project.rusty.parser.hir.expr.Lit;
import org.key_project.rusty.parser.hir.expr.UnOp;

public interface TermKind {
    record Binary(BinOp op, Term left, Term right) implements TermKind {}
    record Unary(UnOp op, Term child) implements TermKind {}
    record Lit(org.key_project.rusty.parser.hir.expr.Lit lit) implements TermKind {}
}
