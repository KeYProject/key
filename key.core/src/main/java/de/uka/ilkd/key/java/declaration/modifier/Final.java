package de.uka.ilkd.key.java.declaration.modifier;


import org.key_project.util.ExtList;

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
    public Final(ExtList children) {
        super(children);
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
