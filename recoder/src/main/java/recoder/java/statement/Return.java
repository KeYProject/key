// This file is part of the RECODER library and protected by the LGPL.

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
