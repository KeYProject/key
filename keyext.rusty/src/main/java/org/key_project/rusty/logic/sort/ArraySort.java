/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.Nullable;

public final class ArraySort extends SortImpl {
    private final Sort elementSort;
    private final int length;

    public ArraySort(Sort elemSort, int length) {
        super(new Name("[" + elemSort + "; " + length + "]"));
        this.elementSort = elemSort;
        this.length = length;
    }

    public Sort getElementSort() {
        return elementSort;
    }

    public int getLength() {
        return length;
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o == null)
            return false;
        if (o == this)
            return true;
        if (!(o instanceof ArraySort as))
            return false;
        return as.elementSort.equals(elementSort) && as.length == length;
    }
}
