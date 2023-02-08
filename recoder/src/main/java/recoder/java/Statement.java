/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
