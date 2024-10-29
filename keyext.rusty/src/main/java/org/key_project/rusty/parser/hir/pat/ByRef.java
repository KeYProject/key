package org.key_project.rusty.parser.hir.pat;

import org.key_project.rusty.parser.hir.HirAdapter;

public interface ByRef {
    record Yes(boolean mut) implements ByRef {}
    record No() implements ByRef {}

    class Adapter extends HirAdapter<ByRef> {
        @Override
        public Class<? extends ByRef> getType(String tag) {
            return switch(tag) {
                case "Yes" -> Yes.class;
                case "No" -> No.class;
                default -> null;
            };
        }
    }
}
