/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression;

import recoder.java.*;
import recoder.java.reference.ReferencePrefix;
import recoder.java.reference.ReferenceSuffix;

/**
 * Redundant Parentheses. Modelled as a special "identity" unary "infix" operator.
 */

public class ParenthesizedExpression extends Operator
        implements ExpressionStatement, ReferencePrefix {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 5087638517523549125L;

    /**
     * Access parent.
     */
    protected ReferenceSuffix accessParent;

    /**
     * Statement parent.
     */
    protected StatementContainer statementParent;

    /**
     * Parenthesized expression.
     */

    public ParenthesizedExpression() {
        // nothing to do
    }

    /**
     * Parenthesized expression.
     *
     * @param child an expression.
     */

    public ParenthesizedExpression(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Parenthesized expression.
     *
     * @param proto a parenthesized expression.
     */
    protected ParenthesizedExpression(ParenthesizedExpression proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */
    public ParenthesizedExpression deepClone() {
        return new ParenthesizedExpression(this);
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */
    public NonTerminalProgramElement getASTParent() {
        if (expressionParent != null) {
            return expressionParent;
        } else if (accessParent != null) {
            return accessParent;
        } else {
            return statementParent;
        }
    }

    /**
     * Get statement container.
     *
     * @return the statement container.
     */
    public StatementContainer getStatementContainer() {
        return statementParent;
    }

    /**
     * Set statement container.
     *
     * @param parent a statement container.
     */
    public void setStatementContainer(StatementContainer parent) {
        statementParent = parent;
        expressionParent = null;
        accessParent = null;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */
    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
        statementParent = null;
        accessParent = null;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (children != null) ? children.size() : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (children != null) {
            return children.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return accessParent;
    }

    /**
     * Set reference suffix.
     *
     * @param path a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix path) {
        accessParent = path;
        expressionParent = null;
        statementParent = null;
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */
    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 0;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
        /* Only unary infix operator;) */
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    public void accept(SourceVisitor v) {
        v.visitParenthesizedExpression(this);
    }
}
