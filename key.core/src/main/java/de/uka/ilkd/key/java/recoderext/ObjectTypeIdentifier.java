/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

public class ObjectTypeIdentifier extends Identifier {

    /**
     *
     */
    private static final long serialVersionUID = -2181868786991278019L;

    public ObjectTypeIdentifier(String id) {
        super(id);
    }

    // protected void setText(String text) {
    // id = text.intern();
    // }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ObjectTypeIdentifier deepClone() {
        return new ObjectTypeIdentifier(id);
    }

}
