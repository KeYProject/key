/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

/**
 * Statement container.
 *
 * @author <TT>AutoDoc</TT>
 */

public interface StatementContainer extends NonTerminalProgramElement {

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    int getStatementCount();

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    Statement getStatementAt(int index);
}
