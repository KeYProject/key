/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableSet;

/**
 * Two kind of matching algorithm are coded in two nested classes BaseMatching TwosideMatching
 */
class Matching {

    private Matching() {}

    /**
     * matching <code>trigger</code> to <code>targetTerm</code> recursively
     *
     * @param trigger a uni-trigger
     * @param targetTerm a gound term
     * @return all substitution found from this matching
     */
    public static ImmutableSet<Substitution> basicMatching(Trigger trigger, Term targetTerm) {
        return BasicMatching.getSubstitutions(trigger.getTriggerTerm(), targetTerm);
    }

    public static ImmutableSet<Substitution> twoSidedMatching(UniTrigger trigger, Term targetTerm,
            Services services) {
        TwoSidedMatching tsm = new TwoSidedMatching(trigger, targetTerm, services);
        return tsm.getSubstitutions(services);
    }

}
