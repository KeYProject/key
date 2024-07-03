/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.logic;

/** BooleanContainer wraps primitive bool */
public final class BooleanContainer {
    private boolean bool;

    public BooleanContainer() {
        bool = false;
    }

    public final boolean val() {
        return bool;
    }

    public final void setVal(boolean b) {
        bool = b;
    }
}
