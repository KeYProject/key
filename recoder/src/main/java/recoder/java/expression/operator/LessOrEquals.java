/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Less or equals.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LessOrEquals extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2156040099278098771L;

    /**
     * Less or equals.
     */

    public LessOrEquals() {
        super();
    }

    /**
     * Less or equals.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public LessOrEquals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Less or equals.
     *
     * @param proto a less or equals.
     */

    protected LessOrEquals(LessOrEquals proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LessOrEquals deepClone() {
        return new LessOrEquals(this);
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
        v.visitLessOrEquals(this);
    }
}
