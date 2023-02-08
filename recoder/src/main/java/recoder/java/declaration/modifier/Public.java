/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

/**
 * Public.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Public extends VisibilityModifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 9023181714825745478L;

    /**
     * Public.
     */

    public Public() {
        // nothing to do
    }

    /**
     * Public.
     *
     * @param proto a public.
     */

    protected Public(Public proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Public deepClone() {
        return new Public(this);
    }

    public void accept(SourceVisitor v) {
        v.visitPublic(this);
    }
}
