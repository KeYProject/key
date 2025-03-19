/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Equals.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Equals extends ComparativeOperator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2291841565483675639L;

    /**
     * Equals.
     */

    public Equals() {
        super();
    }

    /**
     * Equals.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Equals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Equals.
     *
     * @param proto an equals.
     */

    protected Equals(Equals proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Equals deepClone() {
        return new Equals(this);
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
        v.visitEquals(this);
    }
}
