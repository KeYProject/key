/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

import org.key_project.util.ExtList;

/**
 * Abstract.
 */

public class Abstract extends Modifier {

    /**
     * Abstract.
     */
    public Abstract() {}


    /**
     * Abstract.
     *
     * @param children list of children. May contain: Comments
     */
    public Abstract(ExtList children) {
        super(children);
    }



    /**
     * Get symbol.
     *
     * @return the string.
     */
    protected String getSymbol() {
        return "abstract";
    }
}
