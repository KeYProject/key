// This file is part of the RECODER library and protected by the LGPL.

package recoder.java;

/**
 * Statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface Statement extends ProgramElement {

    /**
     * Get statement container.
     *
     * @return the statement container.
     */
    StatementContainer getStatementContainer();

    /**
     * Set statement container.
     *
     * @param c a statement container.
     */
    void setStatementContainer(StatementContainer c);

    Statement deepClone();
}
