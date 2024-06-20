/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

public class SortImpl extends AbstractSort {
    public SortImpl(Name name, boolean isAbstract) {
        super(name, isAbstract);
    }

    public SortImpl(Name name) {
        this(name, false);
    }

    @Override
    public ImmutableSet<Sort> extendsSorts() {
        return null;
    }

    @Override
    public boolean extendsTrans(Sort s) {
        return false;
    }


    @Override
    public String declarationString() {
        return "";
    }
}
