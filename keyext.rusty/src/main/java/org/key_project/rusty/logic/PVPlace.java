/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.op.ProgramVariable;

import org.jspecify.annotations.NonNull;

public class PVPlace extends Place {
    private static final WeakHashMap<ProgramVariable, WeakReference<PVPlace>> instances =
        new WeakHashMap<>();

    private final ProgramVariable pv;

    /**
     * Returns the mut ref operator for the passed left hand side.
     */
    public static PVPlace getInstance(ProgramVariable pv) {
        WeakReference<PVPlace> ref = instances.get(pv);
        PVPlace result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new PVPlace(pv);
            ref = new WeakReference<>(result);
            instances.put(pv, ref);
        }
        return result;
    }

    private PVPlace(ProgramVariable pv) {
        this.pv = pv;
    }

    public ProgramVariable getProgramVariable() {
        return pv;
    }

    @Override
    public @NonNull Sort sort() {
        return pv.sort();
    }

    @Override
    public String toString() {
        return "/" + pv + "/";
    }
}
