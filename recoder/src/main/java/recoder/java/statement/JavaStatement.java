/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.JavaNonTerminalProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.Statement;
import recoder.java.StatementContainer;

/**
 * Default implementation for non-terminal Java statements.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class JavaStatement extends JavaNonTerminalProgramElement implements Statement {

    /**
     * Parent.
     */

    protected StatementContainer parent;

    /**
     * Java statement.
     */

    public JavaStatement() {
        // nothing to do
    }

    /**
     * Java statement.
     *
     * @param proto a java statement.
     */

    protected JavaStatement(JavaStatement proto) {
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
}
