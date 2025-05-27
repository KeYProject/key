/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang.spec;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.QPath;
import org.key_project.rusty.parser.hir.expr.BinOp;
import org.key_project.rusty.parser.hir.expr.Lit;
import org.key_project.rusty.parser.hir.expr.UnOp;

public interface TermKind {
    record Binary(BinOp op, Term left, Term right) implements TermKind {
    }

    record Unary(UnOp op, Term child) implements TermKind {
    }

    record Lit(org.key_project.rusty.parser.hir.expr.Lit lit) implements TermKind {
    }

    record Path(QPath path) implements TermKind {
    }

    class Adapter extends HirAdapter<TermKind> {
        @Override
        public Class<? extends TermKind> getType(String tag) {
            return switch (tag) {
            case "Binary" -> Binary.class;
            case "Unary" -> Unary.class;
            case "Lit" -> Lit.class;
            case "Path" -> Path.class;
            default -> null;
            };
        }

    }
}
