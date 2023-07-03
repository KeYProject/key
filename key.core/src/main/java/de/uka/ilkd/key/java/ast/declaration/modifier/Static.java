package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.declaration.Modifier;

/**
 * Static.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Static extends Modifier {

    /**
     * Static.
     */

    public Static() {}

    /**
     * Static
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */

    public Static(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "static";
    }
}
