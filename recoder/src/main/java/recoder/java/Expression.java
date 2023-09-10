/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

/**
 * General expression. In Java, any {@link recoder.java.expression.Assignment} is also a valid
 * expression.
 *
 * @author AL
 * @author <TT>AutoDoc</TT>
 */

public interface Expression extends ProgramElement {

    /**
     * Get expression container.
     *
     * @return the expression container.
     */
    ExpressionContainer getExpressionContainer();

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */
    void setExpressionContainer(ExpressionContainer c);

    /*
     * make return type Expression
     */
    Expression deepClone();
}
