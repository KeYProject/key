package de.uka.ilkd.key.java.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.declaration.Modifier;

/**
 * Abstract.
 */

public class Abstract extends Modifier {

    /**
     * Abstract.
     */
    public Abstract() {}


    /**
     * Abstract.
     *
     * @param children list of children. May contain: Comments
     */
    public Abstract(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }



    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "abstract";
    }
}
