/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import java.util.Arrays;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.stmt.Stmt;

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
