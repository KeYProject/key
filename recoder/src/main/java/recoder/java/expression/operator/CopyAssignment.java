/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Copy assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class CopyAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7829333990720251044L;

    /**
     * Copy assignment.
     */

    public CopyAssignment() {
        // nothing to do
    }

    /**
     * Copy assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public CopyAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Copy assignment.
     *
     * @param proto a copy assignment.
     */

    protected CopyAssignment(CopyAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public CopyAssignment deepClone() {
        return new CopyAssignment(this);
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
        v.visitCopyAssignment(this);
    }
}
