/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.*;

/**
 * Literal.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class Literal extends JavaProgramElement
        implements Expression, TerminalProgramElement {

    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;

    /**
     * Literal.
     */

    public Literal() {
        // nothing to do
    }

    /**
     * Literal.
     *
     * @param proto a literal.
     */

    protected Literal(Literal proto) {
        super(proto);
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return expressionParent;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
    }

    public abstract Object getEquivalentJavaType();
}
