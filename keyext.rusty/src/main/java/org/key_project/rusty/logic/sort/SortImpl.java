/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.AbstractSort;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public class SortImpl extends AbstractSort {
    private ImmutableSet<Sort> ext;

    public SortImpl(Name name, boolean isAbstract, ImmutableSet<Sort> ext) {
        super(name, isAbstract);
        this.ext = ext;
    }

    public SortImpl(Name name, boolean isAbstract) {
        super(name, isAbstract);
    }

    public SortImpl(Name name) {
        this(name, false);
    }

    @Override
    public @NonNull ImmutableSet<Sort> extendsSorts() {
        if (this == RustyDLTheory.FORMULA || this == RustyDLTheory.UPDATE
                || this == RustyDLTheory.ANY) {
            return DefaultImmutableSet.nil();
        } else {
            if (ext.isEmpty()) {
                ext = DefaultImmutableSet.<Sort>nil().add(RustyDLTheory.ANY);
            }
            return ext;
        }
    }

    @Override
    public boolean extendsTrans(@NonNull Sort sort) {
        if (sort == this) {
            return true;
        } else if (this == RustyDLTheory.FORMULA || this == RustyDLTheory.UPDATE) {
            return false;
        } else if (sort == RustyDLTheory.ANY) {
            return true;
        }

        return extendsSorts()
                .exists((Sort superSort) -> superSort == sort || superSort.extendsTrans(sort));
    }


    @Override
    public @NonNull String declarationString() {
        return "";
    }
}
