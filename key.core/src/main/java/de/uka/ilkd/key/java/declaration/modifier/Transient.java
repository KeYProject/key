package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

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

    public Transient(ExtList children) {
        super(children);
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
