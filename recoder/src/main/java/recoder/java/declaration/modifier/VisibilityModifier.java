/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration.modifier;

import recoder.java.declaration.Modifier;

/**
 * Visibility modifier.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class VisibilityModifier extends Modifier {

    /**
     * Visibility modifier.
     */

    protected VisibilityModifier() {
        // default constructor
    }

    /**
     * Visibility modifier.
     *
     * @param proto a visibility modifier.
     */

    protected VisibilityModifier(VisibilityModifier proto) {
        super(proto);
    }
}
