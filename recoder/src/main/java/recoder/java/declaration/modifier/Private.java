/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration.modifier;

import recoder.java.SourceVisitor;

/**
 * Private.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Private extends VisibilityModifier {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7858559458205603231L;

    /**
     * Private.
     */

    public Private() {
        // nothing to do
    }

    /**
     * Private.
     *
     * @param proto a private.
     */

    protected Private(Private proto) {
        super(proto);
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Private deepClone() {
        return new Private(this);
    }

    public void accept(SourceVisitor v) {
        v.visitPrivate(this);
    }
}
