/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Binary X or assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryXOrAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2881071324012163593L;

    /**
     * Binary X or assignment.
     */

    public BinaryXOrAssignment() {
        // nothing to do
    }

    /**
     * Binary X or assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryXOrAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary X or assignment.
     *
     * @param proto a binary X or assignment.
     */

    protected BinaryXOrAssignment(BinaryXOrAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryXOrAssignment deepClone() {
        return new BinaryXOrAssignment(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 13;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryXOrAssignment(this);
    }
}
