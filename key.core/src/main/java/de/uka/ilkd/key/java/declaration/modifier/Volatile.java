package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;

/**
 * Volatile.
 *
 */

public class Volatile extends Modifier {

    /**
     * Volatile.
     */

    public Volatile() {}

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */
    public Volatile(ExtList children) {
        super(children);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "volatile";
    }
}
