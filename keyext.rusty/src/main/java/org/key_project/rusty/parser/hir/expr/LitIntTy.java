/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.hirty.IntTy;
import org.key_project.rusty.parser.hir.hirty.UintTy;

public interface LitIntTy {
    record Signed(IntTy ty) implements LitIntTy {}

    record Unsigned(UintTy ty) implements LitIntTy {}

    record Unsuffixed() implements LitIntTy {}

    class Adapter extends HirAdapter<LitIntTy> {
        @Override
        public Class<? extends LitIntTy> getType(String tag) {
            return switch (tag) {
                case "Signed" -> Signed.class;
                case "Unsigned" -> Unsigned.class;
                case "Unsuffixed" -> Unsuffixed.class;
                default -> null;
            };
        }
    }
}
