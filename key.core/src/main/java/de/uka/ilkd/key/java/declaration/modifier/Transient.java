package de.uka.ilkd.key.java.declaration.modifier;

import java.util.List;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.declaration.Modifier;

/**
 * Transient.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Transient extends Modifier {

    /**
     * Transient.
     */

    public Transient() {}

    /**
     * Transient.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */

    public Transient(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "transient";
    }
}
