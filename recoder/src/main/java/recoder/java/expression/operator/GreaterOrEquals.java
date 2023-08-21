/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Greater or equals.
 *
 * @author <TT>AutoDoc</TT>
 */

public class GreaterOrEquals extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 7710158660690500126L;

    /**
     * Greater or equals.
     */

    public GreaterOrEquals() {
        super();
    }

    /**
     * Greater or equals.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public GreaterOrEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Greater or equals.
     *
     * @param proto a greater or equals.
     */

    protected GreaterOrEquals(GreaterOrEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public GreaterOrEquals deepClone() {
        return new GreaterOrEquals(this);
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 5;
    }

    public void accept(SourceVisitor v) {
        v.visitGreaterOrEquals(this);
    }
}
