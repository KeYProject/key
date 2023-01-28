// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.statement;

import recoder.java.Identifier;
import recoder.java.SourceVisitor;

/**
 * Break.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Break extends LabelJumpStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6926617993568300612L;

    /**
     * Break.
     */

    public Break() {
        makeParentRoleValid();
    }

    /**
     * Break.
     *
     * @param label an identifier.
     */

    public Break(Identifier label) {
        super(label);
        makeParentRoleValid();
    }

    /**
     * Break.
     *
     * @param proto a break.
     */

    protected Break(Break proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Break deepClone() {
        return new Break(this);
    }

    public void accept(SourceVisitor v) {
        v.visitBreak(this);
    }
}
