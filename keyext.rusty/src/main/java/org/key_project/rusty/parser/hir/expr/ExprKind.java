/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.Label;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.Span;

import org.jspecify.annotations.Nullable;

public interface ExprKind {
    record Call(Expr callee, Expr[]args) implements ExprKind {}

    record Binary(BinOp op, Expr left, Expr right) implements ExprKind {}

    record Unary(UnOp op, Expr expr) implements ExprKind {}

    record LitExpr(Lit lit) implements ExprKind {}

    record DropTemps(Expr expr) implements ExprKind {}

    record Let(LetExpr let) implements ExprKind {}

    record If(Expr cond, Expr then, @Nullable Expr els) implements ExprKind {}

    record Loop(Block block, @Nullable Label label, Span span) implements ExprKind {}

    record BlockExpr(Block block) implements ExprKind {}

    record Assign(Expr left, Expr right, Span span) implements ExprKind {}

    record AssignOp(AssignOperator op, Expr left, Expr right) implements ExprKind {}

    record Path(QPath path) implements ExprKind {}

    record AddrOf(boolean raw, boolean mut, Expr expr) implements ExprKind {}

    record Break(Destination dest, @Nullable Expr expr) implements ExprKind{}

    class Adapter extends HirAdapter<ExprKind> {
        @Override
        public Class<? extends ExprKind> getType(String tag) {
            return switch (tag) {
                case "Call" -> Call.class;
                case "Binary" -> Binary.class;
                case "Unary" -> Unary.class;
                case "Lit" -> LitExpr.class;
                case "DropTemps" -> DropTemps.class;
                case "Let" -> Let.class;
                case "If" -> If.class;
                case "Loop" -> Loop.class;
                case "Block" -> BlockExpr.class;
                case "Assign" -> Assign.class;
                case "AssignOp" -> AssignOp.class;
                case "Path" -> Path.class;
                case "AddrOf" -> AddrOf.class;
                case "Break" -> Break.class;
                default -> null;
            };
        }
    }
}
