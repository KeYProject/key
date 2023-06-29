package de.uka.ilkd.key.java.declaration.modifier;


import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.declaration.Modifier;

/**
 * Final.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Final extends Modifier {

    /**
     * Final.
     */

    public Final() {}

    /**
     * Abstract.
     *
     * @param children list of children. May contain: Comments
     */
    public Final(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "final";
    }
}
