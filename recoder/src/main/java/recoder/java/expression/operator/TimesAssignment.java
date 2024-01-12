/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Times assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class TimesAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1978899655527666905L;

    /**
     * Times assignment.
     */

    public TimesAssignment() {
        // nothing to do
    }

    /**
     * Times assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public TimesAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Times assignment.
     *
     * @param proto a times assignment.
     */

    protected TimesAssignment(TimesAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public TimesAssignment deepClone() {
        return new TimesAssignment(this);
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
        v.visitTimesAssignment(this);
    }
}
