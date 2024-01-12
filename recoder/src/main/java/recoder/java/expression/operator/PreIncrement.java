/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Pre increment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PreIncrement extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1081530758324817367L;

    /**
     * Pre increment.
     */

    public PreIncrement() {
        // nothing to do
    }

    /**
     * Pre increment.
     *
     * @param child an expression.
     */

    public PreIncrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Pre increment.
     *
     * @param proto a pre increment.
     */

    protected PreIncrement(PreIncrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PreIncrement deepClone() {
        return new PreIncrement(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitPreIncrement(this);
    }
}
