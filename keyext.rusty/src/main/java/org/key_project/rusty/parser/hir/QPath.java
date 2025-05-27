/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir;

import org.key_project.rusty.parser.hir.hirty.HirTy;

import org.jspecify.annotations.Nullable;

public interface QPath {
    record Resolved(@Nullable HirTy ty, Path<Res> path) implements QPath {
    }

    record TypeRelative(HirTy ty, PathSegment seg) implements QPath {
    }

    record LangItem(Span span) implements QPath {
    }

    class Adapter extends HirAdapter<QPath> {
        @Override
        public Class<? extends QPath> getType(String tag) {
            return switch (tag) {
            case "Resolved" -> Resolved.class;
            case "TypeRelative" -> TypeRelative.class;
            case "LangItem" -> LangItem.class;
            default -> null;
            };
        }
    }
}
