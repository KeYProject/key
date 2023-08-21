/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Less than.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LessThan extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 4124515513475981206L;

    /**
     * Less than.
     */

    public LessThan() {
        super();
    }

    /**
     * Less than.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public LessThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Less than.
     *
     * @param proto a less than.
     */

    protected LessThan(LessThan proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LessThan deepClone() {
        return new LessThan(this);
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
        v.visitLessThan(this);
    }
}
