package org.key_project.rusty.parser.hir;

import org.key_project.rusty.parser.hir.hirty.PrimHirTy;

public interface Res {
    record PrimTy(PrimHirTy ty) implements Res{}
    record Local(HirId id) implements Res{}

    class Adapter extends HirAdapter<Res> {
        @Override
        public Class<? extends Res> getType(String tag) {
            return switch (tag) {
                case "PrimTy" -> PrimTy.class;
                case "Local" -> Local.class;
                default -> null;
            };
        }
    }
}
