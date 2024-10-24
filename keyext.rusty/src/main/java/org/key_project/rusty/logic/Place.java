/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import org.key_project.logic.Sorted;
import org.key_project.logic.Term;
import org.key_project.rusty.logic.op.ProgramVariable;

/**
 * A place is a program location we can borrow. See {@link org.key_project.rusty.logic.op.MutRef}
 * for its application.
 * At the moment the only places are {@link PVPlace}s.
 * <br>
 * Places are not terms and cannot be changed by updates.
 */
public abstract class Place implements Sorted {
    public static Place convertToPlace(Term t) {
        t = t.sub(0);
        if (t.op() instanceof ProgramVariable pv) {
            return PVPlace.getInstance(pv);
        }
        throw new IllegalArgumentException("Cannot convert " + t + " to a Place");
    }
}
