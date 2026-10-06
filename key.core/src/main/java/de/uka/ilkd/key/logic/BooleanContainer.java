/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

/** BooleanContainer wraps primitive bool */
public final class BooleanContainer {
    private boolean bool;

    public BooleanContainer() {
        bool = false;
    }

    public boolean val() {
        return bool;
    }

    public void setVal(boolean b) {
        bool = b;
    }
}
