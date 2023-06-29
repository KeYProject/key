package de.uka.ilkd.key.java.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.declaration.Modifier;

/**
 * Native.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Native extends Modifier {

    /**
     * Native.
     */

    public Native() {}

    /**
     * Native
     *
     * @param children list of children. May contain: Comments
     */
    public Native(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "native";
    }
}
