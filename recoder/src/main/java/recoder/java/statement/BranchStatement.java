// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.statement;

import recoder.java.NonTerminalProgramElement;

/**
 * Branch statement.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public abstract class BranchStatement extends JavaStatement implements NonTerminalProgramElement {

    /**
     * Branch statement.
     */

    public BranchStatement() {
        // nothing to do
    }

    /**
     * Branch statement.
     *
     * @param proto a branch statement.
     */

    protected BranchStatement(BranchStatement proto) {
        super(proto);
    }

    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    public abstract int getBranchCount();

    /*
     * Return the branch at the specified index in this node's "virtual" branch array. @param index
     * an index for a branch. @return the branch with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public abstract Branch getBranchAt(int index);
}
