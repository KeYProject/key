/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.Identifier;
import recoder.java.SourceVisitor;

/**
 * Continue.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Continue extends LabelJumpStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 8896520115861515813L;

    /**
     * Continue.
     */

    public Continue() {
        // nothing to do
    }

    /**
     * Continue.
     *
     * @param label an identifier.
     */

    public Continue(Identifier label) {
        super(label);
        makeParentRoleValid();
    }

    /**
     * Continue.
     *
     * @param proto a continue.
     */

    protected Continue(Continue proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Continue deepClone() {
        return new Continue(this);
    }

    public void accept(SourceVisitor v) {
        v.visitContinue(this);
    }
}
