/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;
import recoder.list.generic.ASTArrayList;

/**
 * The ternary C-style conditional operator.
 */
public class Conditional extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -3581491297079611854L;

    /**
     * Conditional.
     */

    public Conditional() {
        super();
    }

    /**
     * Conditional.
     *
     * @param guard an expression.
     * @param thenExpr an expression.
     * @param elseExpr an expression.
     */

    public Conditional(Expression guard, Expression thenExpr, Expression elseExpr) {
        children = new ASTArrayList<>(getArity());
        children.add(guard);
        children.add(thenExpr);
        children.add(elseExpr);
        super.makeParentRoleValid();
    }

    /**
     * Conditional.
     *
     * @param proto a conditional.
     */

    protected Conditional(Conditional proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Conditional deepClone() {
        return new Conditional(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 3;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 12;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /**
     * Checks if this operator is left or right associative. Conditionals are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>
     * false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitConditional(this);
    }
}
