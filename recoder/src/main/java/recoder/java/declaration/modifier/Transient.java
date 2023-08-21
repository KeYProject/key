/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;
import recoder.java.declaration.Modifier;

/**
 * Transient.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Transient extends Modifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3518754803226194289L;

    /**
     * Transient.
     */

    public Transient() {
        // nothing to do
    }

    /**
     * Transient.
     *
     * @param proto a transient.
     */

    protected Transient(Transient proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Transient deepClone() {
        return new Transient(this);
    }

    public void accept(SourceVisitor v) {
        v.visitTransient(this);
    }
}
