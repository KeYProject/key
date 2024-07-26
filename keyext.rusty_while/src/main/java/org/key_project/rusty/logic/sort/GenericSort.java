/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.sort;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;
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

    /**
     * @return true if "p_s" is a possible instantiation of this sort. This method does not check
     *         the instantiations of other generic sorts, i.e. the return value true is possible
     *         even if "p_s" is not a valid instantiation.
     *
     *         Use "GenericSortInstantiations" instead
     */
    public boolean isPossibleInstantiation(Sort p_s) {
        return p_s != RustyDLTheory.FORMULA && (oneOf.isEmpty() || oneOf.contains(p_s))
                && checkNonGenericSupersorts(p_s);
    }

    /**
     * @return true iff "p_s" is subsort of every non-generic supersort of this sort
     */
    private boolean checkNonGenericSupersorts(Sort p_s) {
        Iterator<Sort> it = extendsSorts().iterator();
        Sort ss;

        while (it.hasNext()) {
            ss = it.next();
            if (ss instanceof GenericSort) {
                if (!((GenericSort) ss).checkNonGenericSupersorts(p_s)) {
                    return false;
                }
            } else {
                if (!p_s.extendsTrans(ss)) {
                    return false;
                }
            }
        }

        return true;
    }
}
