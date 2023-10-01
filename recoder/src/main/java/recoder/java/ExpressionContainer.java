/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

/**
 * Expression container.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public interface ExpressionContainer extends NonTerminalProgramElement {

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */
    int getExpressionCount();

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    Expression getExpressionAt(int index);
}
