/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

/**
 * Protected.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Protected extends VisibilityModifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 294440790233996705L;

    /**
     * Protected.
     */

    public Protected() {
        // nothing to do
    }

    /**
     * Protected.
     *
     * @param proto a protected.
     */

    protected Protected(Protected proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Protected deepClone() {
        return new Protected(this);
    }

    public void accept(SourceVisitor v) {
        v.visitProtected(this);
    }
}
