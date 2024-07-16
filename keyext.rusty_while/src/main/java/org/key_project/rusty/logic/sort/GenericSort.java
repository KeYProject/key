/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


/**
 * Sort used for generic taclets
 * <br>
 * Within an SVInstantiations-object a generic sort is instantiated by a concrete sort, which has to
 * be a subsort of the instantiations of the supersorts of this sort
 */
public class GenericSort extends SortImpl {
    /**
     * list of sorts this generic sort may be instantiated with; EMPTY_SORT_SORT means that every
     * sort may be used
     */
    private final ImmutableSet<Sort> oneOf;

    /**
     * creates a generic sort
     *
     * @param ext supersorts of this sort, which have to be either concrete sorts or plain generic
     *        sorts (i.e. not collection sorts of generic sorts)
     */
    public GenericSort(Name name, ImmutableSet<Sort> ext, ImmutableSet<Sort> oneOf) {
        super(name, false, ext);
        this.oneOf = oneOf;
        // checkSupersorts();
    }

    public GenericSort(Name name) {
        super(name, false);
        this.oneOf = DefaultImmutableSet.nil();
    }

    /**
     * @return possible instantiations
     */
    public ImmutableSet<Sort> getOneOf() {
        return oneOf;
    }
}
