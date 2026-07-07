/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSet;

/**
 * A trigger built from several uni-trigger {@link #elements} that, taken together, bind all
 * universal variables of a clause. A match requires matching every element and merging their
 * substitutions into one that is consistent and total on {@link #clauseVariables}.
 */
class MultiTrigger implements Trigger {

    /** The uni-trigger elements that jointly have to cover {@link #clauseVariables}. */
    private final ImmutableSet<Trigger> elements;

    /** The universal variables of the clause this multi-trigger must bind. */
    private final ImmutableSet<QuantifiableVariable> clauseVariables;

    private final Term clause;

    MultiTrigger(ImmutableSet<Trigger> elements, ImmutableSet<QuantifiableVariable> clauseVariables,
            Term clause) {
        this.elements = elements;
        this.clauseVariables = clauseVariables;
        this.clause = clause;
    }

    @Override
    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerms,
            Services services) {
        ImmutableList<Substitution> total = ImmutableList.nil();

        final ImmutableSet<Substitution> combined =
            combineElementSubstitutions(elements.iterator(), targetTerms, services);

        for (Substitution sub : combined) {
            if (sub.isTotalOn(clauseVariables)) {
                total = total.prepend(sub);
            }
        }

        return DefaultImmutableSet.fromImmutableList(total);
    }

    /**
     * Matches every remaining element against the target terms and combines the per-element
     * substitution sets by taking the cross product and merging each compatible pair (incompatible
     * pairs are dropped). Used by {@link #getSubstitutionsFromTerms}.
     */
    private ImmutableSet<Substitution> combineElementSubstitutions(
            Iterator<? extends Trigger> remainingElements, ImmutableSet<Term> terms,
            Services services) {
        ImmutableList<Substitution> result = ImmutableList.nil();
        if (remainingElements.hasNext()) {
            ImmutableSet<Substitution> headSubs =
                remainingElements.next().getSubstitutionsFromTerms(terms, services);
            ImmutableSet<Substitution> tailSubs =
                combineElementSubstitutions(remainingElements, terms, services);
            if (tailSubs.isEmpty()) {
                return headSubs;
            } else if (headSubs.isEmpty()) {
                return tailSubs;
            }
            for (Substitution tailSub : tailSubs) {
                for (Substitution headSub : headSubs) {
                    final Substitution merged = mergeIfCompatible(tailSub, headSub);
                    if (merged != null) {
                        result = result.prepend(merged);
                    }
                }

            }
        }
        return DefaultImmutableSet.fromImmutableList(result);
    }

    /**
     * Merges two substitutions: if they bind every shared variable to the same term, returns a new
     * substitution containing all bindings of both; otherwise (a conflicting binding) returns
     * {@code null}.
     */
    private Substitution mergeIfCompatible(Substitution left, Substitution right) {
        final ImmutableMap<QuantifiableVariable, Term> rightMap = right.getVarMap();
        ImmutableMap<QuantifiableVariable, Term> mergedMap = rightMap;

        for (final ImmutableMapEntry<QuantifiableVariable, Term> entry : left.getVarMap()) {
            QuantifiableVariable key = entry.key();
            Term value = entry.value();
            if (rightMap.containsKey(key)) {
                if (!(rightMap.get(key).equals(value))) {
                    return null;
                }
            }
            mergedMap = mergedMap.put(key, value);
        }
        return new Substitution(mergedMap);
    }

    @Override
    public boolean equals(Object other) {
        if (!(other instanceof MultiTrigger otherTrigger)) {
            return false;
        }

        return otherTrigger.elements.equals(elements);
    }

    @Override
    public int hashCode() {
        return elements.hashCode();
    }

    @Override
    public String toString() {
        return String.valueOf(elements);
    }

    @Override
    public Term getTriggerTerm() {
        return clause;
    }

}
