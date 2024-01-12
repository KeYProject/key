/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Synchronized.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Synchronized extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4425302603634609276L;

    /**
     * Synchronized.
     */

    public Synchronized() {
        // nothing to do
    }

    /**
     * Synchronized.
     *
     * @param proto a synchronized.
     */

    protected Synchronized(Synchronized proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Synchronized deepClone() {
        return new Synchronized(this);
    }

    public void accept(SourceVisitor v) {
        v.visitSynchronized(this);
    }

}
