package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

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
    public Native(ExtList children) {
        super(children);
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
