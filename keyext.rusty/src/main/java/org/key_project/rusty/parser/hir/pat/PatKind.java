/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.pat;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Ident;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.expr.Expr;

import org.jspecify.annotations.Nullable;

public interface PatKind {
    record Wild() implements PatKind {}

    record Binding(BindingMode mode, HirId hirId, Ident ident, Pat pat) implements PatKind{}

    record Path(QPath path) implements PatKind {}

    record Range(@Nullable Expr lhs, @Nullable Expr rhs, boolean inclusive) implements PatKind {}

    class Adapter extends HirAdapter<PatKind> {
        @Override
        public Class<? extends PatKind> getType(String tag) {
            return switch (tag) {
                case "Wild" -> Wild.class;
                case "Binding" -> Binding.class;
                case "Path" -> Path.class;
                case "Range" -> Range.class;
                default -> null;
            };
        }
    }
}
