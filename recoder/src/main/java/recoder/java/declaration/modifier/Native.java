/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Native.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Native extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5292363142166406788L;

    /**
     * Native.
     */

    public Native() {
        // nothing to do
    }

    /**
     * Native.
     *
     * @param proto a native.
     */

    protected Native(Native proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Native deepClone() {
        return new Native(this);
    }

    public void accept(SourceVisitor v) {
        v.visitNative(this);
    }
}
