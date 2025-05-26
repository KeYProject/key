/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.pat;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.QPath;

public interface PatExprKind {
    record Lit(org.key_project.rusty.parser.hir.expr.Lit lit, boolean negated) implements PatExprKind {}

    record Path(QPath path) implements PatExprKind {}

    class Adapter extends HirAdapter<PatExprKind> {
        @Override
        public Class<? extends PatExprKind> getType(String tag) {
            return switch (tag) {
                case "Lit" -> PatExprKind.Lit.class;
                case "Path" -> PatExprKind.Path.class;
                default -> null;
            };
        }
    }
}
