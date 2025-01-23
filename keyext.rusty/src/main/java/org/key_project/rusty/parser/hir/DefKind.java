/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir;

public interface DefKind {
    record Mod() implements DefKind {}

    record Fn() implements DefKind {}

    record AssocFn() implements DefKind {}

    record Trait() implements DefKind {}

    record Struct() implements DefKind {}

    record Enum() implements DefKind {}

    record Const() implements DefKind {}

    record Union() implements DefKind {}

    class Adapter extends HirAdapter<DefKind> {
        @Override
        public Class<? extends DefKind> getType(String tag) {
            return switch (tag) {
                case "Mod" -> Mod.class;
                case "Fn" -> Fn.class;
                case "AssocFn" -> AssocFn.class;
                case "Trait" -> Trait.class;
                case "Struct" -> Struct.class;
                case "Enum" -> Enum.class;
                case "Const" -> Const.class;
                case "Union" -> Union.class;
                default -> null;
            };
        }
    }
}
