package org.key_project.rusty.parser.hir.stmt;

import org.key_project.rusty.parser.hir.HirAdapter;
import org.key_project.rusty.parser.hir.expr.Expr;
import org.key_project.rusty.parser.hir.item.Item;

public interface StmtKind {
    record Let(LetStmt let) implements StmtKind {}
    record ItemStmt(Item item) implements StmtKind {}
    record ExprStmt(Expr expr) implements StmtKind {}
    record Semi(Expr expr) implements StmtKind {}

    class Adapter extends HirAdapter<StmtKind> {
        @Override
        public Class<? extends StmtKind> getType(String tag) {
            return switch (tag)  {
                case "Let" -> Let.class;
                case "Item" -> ItemStmt.class;
                case "Expr" -> ExprStmt.class;
                case "Semi" -> Semi.class;
                default -> null;
            };
        }
    }
}
