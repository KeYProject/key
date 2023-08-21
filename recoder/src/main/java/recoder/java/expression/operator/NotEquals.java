/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Not equals.
 *
 * @author <TT>AutoDoc</TT>
 */

public class NotEquals extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4821815905384213846L;

    /**
     * Not equals.
     */

    public NotEquals() {
        super();
    }

    /**
     * Not equals.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public NotEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Not equals.
     *
     * @param proto a not equals.
     */

    protected NotEquals(NotEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public NotEquals deepClone() {
        return new NotEquals(this);
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 6;
    }

    public void accept(SourceVisitor v) {
        v.visitNotEquals(this);
    }
}
