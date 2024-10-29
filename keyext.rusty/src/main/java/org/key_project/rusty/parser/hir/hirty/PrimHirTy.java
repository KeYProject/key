package org.key_project.rusty.parser.hir.hirty;

import org.key_project.rusty.parser.hir.HirAdapter;

public interface PrimHirTy {
    record Uint(UintTy ty) implements PrimHirTy {}
    record Bool() implements PrimHirTy {}

    class Adapter extends HirAdapter<PrimHirTy>  {
        @Override
        public Class<? extends PrimHirTy> getType(String tag) {
            return switch (tag) {
                case "Uint" -> Uint.class;
                case "Bool" -> Bool.class;
                default -> null;
            };
        }
    }
}
