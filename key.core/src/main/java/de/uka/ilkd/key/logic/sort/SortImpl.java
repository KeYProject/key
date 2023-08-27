/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Standard implementation of the Sort interface.
 */
public final class SortImpl extends AbstractSort {

    public SortImpl(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
        super(name, ext, isAbstract);
    }

    public SortImpl(Name name, ImmutableSet<Sort> ext) {
        this(name, ext, false);
    }

    public SortImpl(Name name, Sort ext) {
        this(name, DefaultImmutableSet.<Sort>nil().add(ext), false);
    }


    public SortImpl(Name name) {
        this(name, DefaultImmutableSet.nil());
    }

    public boolean equals(Object o) {
        if (o instanceof SortImpl) {
            return ((SortImpl) o).name().equals(name());
        } else {
            return false;
        }
    }

}
