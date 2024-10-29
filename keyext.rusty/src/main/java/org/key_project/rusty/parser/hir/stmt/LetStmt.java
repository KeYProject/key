package org.key_project.rusty.parser.hir.stmt;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.expr.Block;
import org.key_project.rusty.parser.hir.expr.Expr;
import org.key_project.rusty.parser.hir.hirty.HirTy;
import org.key_project.rusty.parser.hir.pat.Pat;

public record LetStmt(Pat pat, HirTy ty, Expr init, Block els, HirId hirId, Span span, LocalSource src) {
}
