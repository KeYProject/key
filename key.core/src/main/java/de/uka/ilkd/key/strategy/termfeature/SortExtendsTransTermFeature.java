/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Term feature for testing whether the sort of a term is a subsort of a given sort (or exactly the
 * given sort).
 */
public class SortExtendsTransTermFeature extends BinaryTermFeature {

    private final Sort sort;

    public static TermFeature create(Sort sort) {
        return new SortExtendsTransTermFeature(sort);
    }

    private SortExtendsTransTermFeature(Sort sort) {
        this.sort = sort;
    }

    protected boolean filter(Term term, Services services) {
        return term.sort().extendsTrans(sort);
    }

}
