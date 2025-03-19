/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Greater than.
 *
 * @author <TT>AutoDoc</TT>
 */

public class GreaterThan extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5808604922619258847L;

    /**
     * Greater than.
     */

    public GreaterThan() {
        super();
    }

    /**
     * Greater than.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public GreaterThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Greater than.
     *
     * @param proto a greater than.
     */

    protected GreaterThan(GreaterThan proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public GreaterThan deepClone() {
        return new GreaterThan(this);
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
        v.visitGreaterThan(this);
    }
}
