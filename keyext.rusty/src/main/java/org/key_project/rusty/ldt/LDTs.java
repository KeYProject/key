/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ldt;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

import org.jspecify.annotations.NonNull;

public class LDTs implements Iterable<LDT> {
    private final BoolLDT boolLDT;
    private final IntLDT intLDT;;
    private final Map<Name, LDT> map;

    public LDTs(Services services) {
        boolLDT = new BoolLDT(services);
        intLDT = new IntLDT(services);
        map = new HashMap<>();
        map.put(boolLDT.name(), boolLDT);
        map.put(intLDT.name(), intLDT);
    }

    public BoolLDT getBoolLDT() {
        return boolLDT;
    }

    public IntLDT getIntLDT() {
        return intLDT;
    }

    public LDT get(Name name) {
        return map.get(name);
    }


    @Override
    public @NonNull Iterator<LDT> iterator() {
        return map.values().iterator();
    }

    public LDT getLDTFor(Sort s) {
        for (LDT ldt : this) {
            if (s.equals(ldt.targetSort())) {
                return ldt;
            }
        }
        return null;
    }
}
