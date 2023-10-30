/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.declaration.modifier;

import org.key_project.util.ExtList;

/**
 * Protected.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Protected extends VisibilityModifier {

    /**
     * Protected.
     */

    public Protected() {}

    /**
     * Protected.
     *
     * @param children list of children. May contain: Comments
     */

    public Protected(ExtList children) {
        super(children);
    }


    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected String getSymbol() {
        return "protected";
    }

    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) {
            return -2;
        }
        if (arg0 == null) {
            return -1;
        }
        if (arg0 instanceof Protected) {
            return 0;
        }
        if (arg0 instanceof Public) {
            return 1;
        }
        assert false;
        return 0;
    }
}
