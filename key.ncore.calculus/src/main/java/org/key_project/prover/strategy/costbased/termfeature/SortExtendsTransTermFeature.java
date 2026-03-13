/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.strategy.costbased.MutableState;


/// Term feature for testing whether the sort of a term is a subsort of a given sort (or exactly the
/// given sort).
public class SortExtendsTransTermFeature extends BinaryTermFeature {

    private final Sort sort;

    public static TermFeature create(Sort sort) {
        return new SortExtendsTransTermFeature(sort);
    }

    private SortExtendsTransTermFeature(Sort sort) {
        this.sort = sort;
    }

    @Override
    protected boolean filter(Term term, MutableState mState, LogicServices services) {
        return term.sort().extendsTrans(sort);
    }

}
