/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;


/**
 * A trigger consisting of a single term. Matching it against a target term yields the substitutions
 * for the quantified variables; results are cached per target term.
 */
class UniTrigger implements Trigger {

    private final Term trigger;
    /** The universal variables this trigger binds. */
    private final ImmutableSet<QuantifiableVariable> universalVariables;

    private final TriggersSet owningTriggerSet;

    /**
     * If {@code true} the trigger carries a non-universal (existential) variable and may therefore
     * only be matched by (two-sided) unification, not by basic matching.
     */
    private final boolean onlyUnify;
    private final boolean isElementOfMultitrigger;

    private final LRUCache<Term, ImmutableSet<Substitution>> matchResults =
        new LRUCache<>(1000);

    UniTrigger(Term trigger, ImmutableSet<QuantifiableVariable> universalVariables,
            boolean onlyUnify,
            boolean isElementOfMultitrigger, TriggersSet owningTriggerSet) {
        this.trigger = trigger;
        this.universalVariables = universalVariables;
        this.onlyUnify = onlyUnify;
        this.isElementOfMultitrigger = isElementOfMultitrigger;
        this.owningTriggerSet = owningTriggerSet;
    }

    @Override
    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerms,
            Services services) {
        ImmutableSet<Substitution> allSubs = DefaultImmutableSet.nil();
        for (Term target : targetTerms) {
            allSubs = allSubs.union(cachedSubstitutionsForTerm(target, services));
        }
        return allSubs;
    }

    private ImmutableSet<Substitution> cachedSubstitutionsForTerm(Term target, Services services) {
        ImmutableSet<Substitution> subs = matchResults.get(target);
        if (subs == null) {
            subs = computeSubstitutionsForTerm(target, services);
            matchResults.put(target, subs);
        }
        return subs;
    }

    private ImmutableSet<Substitution> computeSubstitutionsForTerm(Term target, Services services) {
        ImmutableSet<Substitution> subs = DefaultImmutableSet.nil();
        if (target.freeVars().size() > 0 || target.op() instanceof Quantifier) {
            subs = Matching.twoSidedMatching(this, target, services);
        } else if (!onlyUnify) {
            subs = Matching.basicMatching(this, target);
        }
        return subs;
    }


    @Override
    public Term getTriggerTerm() {
        return trigger;
    }

    public boolean equals(Object other) {
        if (!(other instanceof UniTrigger otherTrigger)) {
            return false;
        }
        return otherTrigger.trigger.equals(trigger);
    }

    public int hashCode() {
        return trigger.hashCode();
    }

    public String toString() {
        return String.valueOf(trigger);
    }

    ImmutableSet<QuantifiableVariable> getUniVariables() {
        return universalVariables;
    }

    public TriggersSet getTriggerSetThisBelongsTo() {
        return owningTriggerSet;
    }



    /**
     * Loop test: reject a candidate trigger if matching it against the search term produces a
     * substitution that defines some variable cyclically in terms of itself (which would loop
     * during instantiation). Uses the same matching as basic matching to find the substitutions.
     */
    public static boolean passedLoopTest(Term candidate, Term searchTerm) {
        final ImmutableSet<Substitution> substitutions =
            BasicMatching.getSubstitutions(candidate, searchTerm);

        for (Substitution substitution : substitutions) {
            if (containsCycle(substitution)) {
                return false;
            }
        }
        return true;
    }

    /** Whether some variable of the substitution is (transitively) defined in terms of itself. */
    private static boolean containsCycle(Substitution substitution) {
        final var keys = substitution.getVarMap().keyIterator();
        while (keys.hasNext()) {
            if (reachesItself(substitution.getVarMap(), keys.next())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Worklist reachability check (originally adapted from EqualityConstraint): starting from the
     * term bound to {@code var}, follow variable bindings transitively and report whether
     * {@code var}
     * is reached again -- i.e. whether its definition is cyclic.
     */
    private static boolean reachesItself(
            ImmutableMap<QuantifiableVariable, Term> varMap,
            QuantifiableVariable var) {
        ImmutableList<QuantifiableVariable> visited = ImmutableList.nil();
        ImmutableList<Term> pending = ImmutableList.nil();
        Term current = varMap.get(var);

        if (current.op() == var) {
            return false;
        }

        while (true) {
            for (var freeVar : current.freeVars()) {
                if (!visited.contains(freeVar)) {
                    final var boundTerm = (JTerm) varMap.get(freeVar);
                    if (boundTerm != null) {
                        if (boundTerm.freeVars().contains(var)) {
                            return true;
                        }
                        pending = pending.prepend(boundTerm);
                    }

                    if (freeVar == var) {
                        return true;
                    }

                    visited = visited.prepend(freeVar);
                }
            }

            if (pending.isEmpty()) {
                return false;
            }

            current = pending.head();
            pending = pending.tail();
        }
    }

    boolean isElementOfMultitrigger() {
        return isElementOfMultitrigger;
    }


}
