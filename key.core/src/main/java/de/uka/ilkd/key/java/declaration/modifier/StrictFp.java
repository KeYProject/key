package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;


/**
 * Strict fp.
 *
 * @author <TT>AutoDoc</TT>
 */

public class StrictFp extends Modifier {

    /**
     * Strict fp.
     */

    public StrictFp() {}

    /**
     * Strict fp.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments
     */

    public StrictFp(ExtList children) {
        super(children);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "strictfp";
    }
}
