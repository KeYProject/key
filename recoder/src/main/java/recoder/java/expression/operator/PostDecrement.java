/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Post decrement.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PostDecrement extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1562954246447453685L;

    /**
     * Post decrement.
     */

    public PostDecrement() {
        // nothing to do
    }

    /**
     * Post decrement.
     *
     * @param child an expression.
     */

    public PostDecrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Post decrement.
     *
     * @param proto a post decrement.
     */

    protected PostDecrement(PostDecrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PostDecrement deepClone() {
        return new PostDecrement(this);
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
        return POSTFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitPostDecrement(this);
    }
}
