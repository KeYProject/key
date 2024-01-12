/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Post increment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class PostIncrement extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 4938790165047335376L;

    /**
     * Post increment.
     */

    public PostIncrement() {
        // nothing to do
    }

    /**
     * Post increment.
     *
     * @param child an expression.
     */

    public PostIncrement(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Post increment.
     *
     * @param proto a post increment.
     */

    protected PostIncrement(PostIncrement proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PostIncrement deepClone() {
        return new PostIncrement(this);
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
        v.visitPostIncrement(this);
    }
}
