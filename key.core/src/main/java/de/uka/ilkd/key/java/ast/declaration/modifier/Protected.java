package de.uka.ilkd.key.java.ast.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;

/**
 * Protected.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Protected extends VisibilityModifier {

    /**
     * Protected.
     */

    public Protected() {}

    /**
     * Protected.
     *
     * @param children list of children. May contain: Comments
     */

    public Protected(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "protected";
    }

    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) {
            return -2;
        }
        if (arg0 == null) {
            return -1;
        }
        if (arg0 instanceof Protected) {
            return 0;
        }
        if (arg0 instanceof Public) {
            return 1;
        }
        assert false;
        return 0;
    }
}
