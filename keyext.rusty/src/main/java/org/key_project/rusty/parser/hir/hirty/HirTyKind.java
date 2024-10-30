/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.hirty;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.QPath;

public interface HirTyKind {
    record Path(QPath path) implements HirTyKind {}

    class Adapter extends HirAdapter<HirTyKind> {
        @Override
        public Class<? extends HirTyKind> getType(String tag) {
            return switch (tag) {
                case "Path" -> Path.class;
                default -> null;
            };
        }
    }
}
