/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirAdapter;

public interface LitKind {
    record Int(int value, LitIntTy ty) implements LitKind {}

    record Bool(boolean value) implements LitKind {}

    class Adapter extends HirAdapter<LitKind> {
        @Override
        public Class<? extends LitKind> getType(String tag) {
            return switch (tag) {
                case "Int" -> Int.class;
                case "Bool" -> Bool.class;
                default -> null;
            };
        }
    }
}
