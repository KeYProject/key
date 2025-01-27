/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.ty;

import org.key_project.rusty.parser.hir.DefId;
import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.hirty.IntTy;
import org.key_project.rusty.parser.hir.hirty.UintTy;

public interface Ty {
    record Bool() implements Ty {}

    record Char() implements Ty {}

    record Int(IntTy ty) implements Ty {}

    record Uint(UintTy ty) implements Ty {}

    record Ref(Ty ty, boolean mut) implements Ty {}

    record FnDef(DefId defId) implements Ty {}

    record Closure(DefId defId) implements Ty {}

    record Never() implements Ty {}

    record Tuple(Ty[] tys) implements Ty {}

    record Adt() implements Ty {}

    class Adapter extends HirAdapter<Ty> {
        @Override
        public Class<? extends Ty> getType(String tag) {
            return switch (tag){
                case "Bool" -> Bool.class;
                case "Char" -> Char.class;
                case "Int" -> Int.class;
                case "Uint" -> Uint.class;
                case "Ref" -> Ref.class;
                case "FnDef" -> FnDef.class;
                case "Closure" -> Closure.class;
                case "Never" -> Never.class;
                case "Tuple" -> Tuple.class;
                case "Adt" -> Adt.class;
                default -> null;
            };
        }
    }
}
