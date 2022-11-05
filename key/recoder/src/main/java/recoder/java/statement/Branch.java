// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.statement;

import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.StatementContainer;

/**
 * Branch.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class Branch extends JavaNonTerminalProgramElement implements StatementContainer {

    /**
     * Parent.
     */

    protected BranchStatement parent;

    /**
     * Branch.
     */

    public Branch() {
        super();
    }

    /**
     * Branch.
     *
     * @param proto a branch.
     */

    protected Branch(Branch proto) {
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
     * @return the branch statement.
     */

    public BranchStatement getParent() {
        return parent;
    }
}
