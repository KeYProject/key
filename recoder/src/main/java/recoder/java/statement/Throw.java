/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceVisitor;

/**
 * Throw.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Throw extends ExpressionJumpStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -259489032726058910L;

    /**
     * Throw.
     */

    public Throw() {
        // nothing to do
    }

    /**
     * Throw.
     *
     * @param expr an expression.
     */

    public Throw(Expression expr) {
        super(expr);
        if (expr == null) {
            throw new IllegalArgumentException("Throw requires one argument");
        }
        makeParentRoleValid();
    }

    /**
     * Throw.
     *
     * @param proto a throw.
     */

    protected Throw(Throw proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Throw deepClone() {
        return new Throw(this);
    }

    public void accept(SourceVisitor v) {
        v.visitThrow(this);
    }
}
