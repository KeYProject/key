/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.op.sv.ProgramSV;

import org.jspecify.annotations.NonNull;

public class SVPlace extends Place {
    private static final WeakHashMap<ProgramSV, WeakReference<SVPlace>> instances =
        new WeakHashMap<>();

    private final ProgramSV sv;

    /**
     * Returns the mut ref operator for the passed left hand side.
     */
    public static SVPlace getInstance(ProgramSV sv) {
        WeakReference<SVPlace> ref = instances.get(sv);
        SVPlace result = null;
        if (ref != null) {
            result = ref.get();
        }
        if (result == null) {
            result = new SVPlace(sv);
            ref = new WeakReference<>(result);
            instances.put(sv, ref);
        }
        return result;
    }

    private SVPlace(ProgramSV pv) {
        this.sv = pv;
    }

    public ProgramSV getSchemaVariable() {
        return sv;
    }

    @Override
    public @NonNull Sort sort() {
        return sv.sort();
    }

    @Override
    public String toString() {
        return "/" + sv + "/";
    }
}
