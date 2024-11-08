/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir;

public interface DefKind {
    record Mod() implements DefKind {}

    record Fn() implements DefKind {}

    class Adapter extends HirAdapter<DefKind> {
        @Override
        public Class<? extends DefKind> getType(String tag) {
            return switch (tag) {
                case "Mod" -> Mod.class;
                case "Fn" -> Fn.class;
                default -> null;
            };
        }
    }
}
