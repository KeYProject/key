package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.stmt.Stmt;

import java.util.Arrays;

public record Block(Stmt[] stmts, Expr expr, HirId hirId, BlockCheckMode rules, Span span, boolean targetedByBreak) {
    @Override
    public String toString() {
        return "Block{" +
                "stmts=" + Arrays.toString(stmts) +
                ", expr=" + expr +
                ", hirId=" + hirId +
                ", rules=" + rules +
                ", span=" + span +
                ", targetedByBreak=" + targetedByBreak +
                '}';
    }
}
