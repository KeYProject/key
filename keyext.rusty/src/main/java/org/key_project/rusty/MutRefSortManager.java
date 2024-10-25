/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.util.HashMap;
import java.util.Map;

import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.sort.MRefSort;

public class MutRefSortManager {
    private final Map<Sort, MRefSort> map = new HashMap<>();

    private final Services services;

    public MutRefSortManager(Services services) {
        this.services = services;
    }

    public Sort getMRefSort(Sort sort) {
        return map.computeIfAbsent(sort,
            s -> {
                MRefSort mRefSort = new MRefSort(s);
                services.getNamespaces().sorts().add(mRefSort);
                return mRefSort;
            });
    }

    public boolean isMRefOf(Sort mRefS, Sort sort) {
        return map.get(mRefS).equals(sort);
    }
}
