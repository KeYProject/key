/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;

public class SRefSort extends SortImpl {
    private final Sort inner;

    /**
     * Should only be created in {@link org.key_project.rusty.Services}
     *
     * @param inner inner sort
     */
    public SRefSort(Sort inner) {
        super(new Name("SRef<" + inner + ">"));
        this.inner = inner;
    }

    public Sort getInner() {
        return inner;
    }
}
