// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration;

import recoder.java.Declaration;
import recoder.java.JavaProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.TerminalProgramElement;

/**
 * Modifier.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class Modifier extends JavaProgramElement
        implements DeclarationSpecifier, TerminalProgramElement {

    /**
     * Parent.
     */

    protected Declaration parent;

    /**
     * Modifier.
     */

    public Modifier() {
        // nothing to do here
    }

    /**
     * Modifier.
     *
     * @param proto a modifier.
     */

    protected Modifier(Modifier proto) {
        super(proto);
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    /**
     * Get parent.
     *
     * @return the declaration.
     */

    public Declaration getParentDeclaration() {
        return parent;
    }

    /**
     * Set parent.
     *
     * @param parent a declaration.
     */

    public void setParent(Declaration parent) {
        this.parent = parent;
    }

}
