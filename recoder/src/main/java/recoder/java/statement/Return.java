/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Return.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Return extends ExpressionJumpStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1L;

    /**
     * Return.
     */

    public Return() {
        // nothing to do
    }

    /**
     * Return.
     *
     * @param expr an expression.
     */

    public Return(Expression expr) {
        super(expr);
        makeParentRoleValid();
    }

    /**
     * Return.
     *
     * @param proto a return.
     */

    protected Return(Return proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Return deepClone() {
        return new Return(this);
    }

    public void accept(SourceVisitor v) {
        v.visitReturn(this);
    }
}
