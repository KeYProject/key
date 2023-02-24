// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.statement;

import recoder.java.*;

/**
 * Empty statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public class EmptyStatement extends JavaProgramElement
        implements Statement, TerminalProgramElement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 7235639345998336043L;
    /**
     * Parent.
     */

    protected StatementContainer parent;

    /**
     * Empty statement.
     */

    public EmptyStatement() {
        super();
    }

    /**
     * Empty statement.
     *
     * @param proto an empty statement.
     */

    protected EmptyStatement(EmptyStatement proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public EmptyStatement deepClone() {
        return new EmptyStatement(this);
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
     * Get statement container.
     *
     * @return the statement container.
     */

    public StatementContainer getStatementContainer() {
        return parent;
    }

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */

    public void setStatementContainer(StatementContainer c) {
        parent = c;
    }

    public void accept(SourceVisitor v) {
        v.visitEmptyStatement(this);
    }
}
