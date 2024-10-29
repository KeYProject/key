package org.key_project.rusty.parser.hir.expr;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.hirty.UintTy;

public interface LitIntTy {
    record Unsigned(UintTy ty) implements LitIntTy {}
    record Unsuffixed() implements LitIntTy {}

    class Adapter extends HirAdapter<LitIntTy> {
        @Override
        public Class<? extends LitIntTy> getType(String tag) {
            return switch (tag) {
                case "Unsigned" -> Unsigned.class;
                case "Unsuffixed" -> Unsuffixed.class;
                default -> null;
            };
        }
    }
}
