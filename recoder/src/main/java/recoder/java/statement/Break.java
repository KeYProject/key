/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
