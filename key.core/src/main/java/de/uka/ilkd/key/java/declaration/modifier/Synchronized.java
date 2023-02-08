package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.declaration.Modifier;

/**
 * Synchronized.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Synchronized extends Modifier {

    /**
     * Synchronized.
     */

    public Synchronized() {}

    /**
     * Synchronized.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */

    public Synchronized(ExtList children) {
        super(children);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "synchronized";
    }
}
