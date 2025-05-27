/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.stmt;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.Span;

public interface LocalSource {
    record Normal() implements LocalSource {
    }

    record AsyncFn() implements LocalSource {
    }

    record AwaitDesugar() implements LocalSource {
    }

    record AssignDesugar(Span span) implements LocalSource {
    }

    class Adapter extends HirAdapter<LocalSource> {
        @Override
        public Class<? extends LocalSource> getType(String tag) {
            return switch (tag) {
            case "Normal" -> Normal.class;
            case "AsyncFn" -> AsyncFn.class;
            case "AwaitDesugar" -> AwaitDesugar.class;
            case "AssignDesugar" -> AssignDesugar.class;
            default -> null;
            };
        }
    }
}
