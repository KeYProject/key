/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirAdapter;

public interface BlockCheckMode {
    record DefaultBlock() implements BlockCheckMode {
    }

    record UnsafeBlock(UnsafeSource src) implements BlockCheckMode {
    }

    class Adapter extends HirAdapter<BlockCheckMode> {
        @Override
        public Class<? extends BlockCheckMode> getType(String tag) {
            return switch (tag) {
            case "DefaultBlock" -> DefaultBlock.class;
            case "UnsafeBlock" -> UnsafeBlock.class;
            default -> null;
            };
        }
    }
}
