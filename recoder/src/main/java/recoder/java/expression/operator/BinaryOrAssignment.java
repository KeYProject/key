/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Binary or assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryOrAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 8200577893328544765L;

    /**
     * Binary or assignment.
     */

    public BinaryOrAssignment() {
        // nothing to do
    }

    /**
     * Binary or assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryOrAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary or assignment.
     *
     * @param proto a binary or assignment.
     */

    protected BinaryOrAssignment(BinaryOrAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryOrAssignment deepClone() {
        return new BinaryOrAssignment(this);
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
        v.visitBinaryOrAssignment(this);
    }
}
