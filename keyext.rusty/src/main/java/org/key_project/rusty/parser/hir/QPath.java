package org.key_project.rusty.parser.hir;

import org.key_project.rusty.parser.hir.hirty.HirTy;

public interface QPath {
    record Resolved(HirTy ty, Path<Res> path)implements QPath {}

    class Adapter extends HirAdapter<QPath> {
        @Override
        public Class<? extends QPath> getType(String tag) {
            return switch (tag) {
                case "Resolved" -> Resolved.class;
                default -> null;
            };
        }
    }
}
