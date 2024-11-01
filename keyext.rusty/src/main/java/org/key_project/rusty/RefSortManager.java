/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.util.HashMap;
import java.util.Map;

import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.sort.MRefSort;
import org.key_project.rusty.logic.sort.SRefSort;

public class RefSortManager {
    private final Map<Sort, MRefSort> mRefMap = new HashMap<>();
    private final Map<Sort, SRefSort> sRefMap = new HashMap<>();

    private final Services services;

    public RefSortManager(Services services) {
        this.services = services;
    }

    public Sort getRefSort(Sort sort, boolean mut) {
        if (mut) {
            return mRefMap.computeIfAbsent(sort,
                s -> {
                    var ms = new MRefSort(s);
                    services.getNamespaces().sorts().add(ms);
                    return ms;
                });
        }
        return sRefMap.computeIfAbsent(sort,
            s -> {
                var ss = new SRefSort(s);
                services.getNamespaces().sorts().add(ss);
                return ss;
            });
    }

    public boolean isMRefOf(Sort mRefS, Sort sort) {
        return mRefMap.get(mRefS).equals(sort);
    }

    public boolean isSRefOf(Sort sRefS, Sort sort) { return sRefMap.get(sRefS).equals(sort); }
}
