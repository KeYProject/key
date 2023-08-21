/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Pre decrement.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PreDecrement extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7068320649989091567L;

    /**
     * Pre decrement.
     */

    public PreDecrement() {
        // nothing to do
    }

    /**
     * Pre decrement.
     *
     * @param child an expression.
     */

    public PreDecrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Pre decrement.
     *
     * @param proto a pre decrement.
     */

    protected PreDecrement(PreDecrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PreDecrement deepClone() {
        return new PreDecrement(this);
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
        v.visitPreDecrement(this);
    }
}
