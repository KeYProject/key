/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;


class UniTrigger implements Trigger {

    private final Term trigger;
    private final ImmutableSet<QuantifiableVariable> uqvs;

    private final TriggersSet triggerSetThisBelongsTo;

    private final boolean onlyUnify;
    private final boolean isElementOfMultitrigger;

    private final LRUCache<Term, ImmutableSet<Substitution>> matchResults =
        new LRUCache<>(1000);

    UniTrigger(Term trigger, ImmutableSet<QuantifiableVariable> uqvs, boolean isUnify,
            boolean isElementOfMultitrigger, TriggersSet triggerSetThisBelongsTo) {
        this.trigger = trigger;
        this.uqvs = uqvs;
        this.onlyUnify = isUnify;
        this.isElementOfMultitrigger = isElementOfMultitrigger;
        this.triggerSetThisBelongsTo = triggerSetThisBelongsTo;
    }

    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerm,
            Services services) {
        ImmutableSet<Substitution> allsubs = DefaultImmutableSet.nil();
        for (Term aTargetTerm : targetTerm) {
            allsubs = allsubs.union(getSubstitutionsFromTerm(aTargetTerm, services));
        }
        return allsubs;
    }

    private ImmutableSet<Substitution> getSubstitutionsFromTerm(Term t, Services services) {
        ImmutableSet<Substitution> res = matchResults.get(t);
        if (res == null) {
            res = getSubstitutionsFromTermHelp(t, services);
            matchResults.put(t, res);
        }
        return res;
    }

    private ImmutableSet<Substitution> getSubstitutionsFromTermHelp(Term t, Services services) {
        ImmutableSet<Substitution> newSubs = DefaultImmutableSet.nil();
        if (t.freeVars().size() > 0 || t.op() instanceof Quantifier) {
            newSubs = Matching.twoSidedMatching(this, t, services);
        } else if (!onlyUnify) {
            newSubs = Matching.basicMatching(this, t);
        }
        return newSubs;
    }


    public Term getTriggerTerm() {
        return trigger;
    }

    public boolean equals(Object arg0) {
        if (!(arg0 instanceof UniTrigger)) {
            return false;
        }
        final UniTrigger a = (UniTrigger) arg0;
        return a.trigger.equals(trigger);
    }

    public int hashCode() {
        return trigger.hashCode();
    }

    public String toString() {
        return String.valueOf(trigger);
    }

    ImmutableSet<QuantifiableVariable> getUniVariables() {
        return uqvs;
    }

    public TriggersSet getTriggerSetThisBelongsTo() {
        return triggerSetThisBelongsTo;
    }



    /**
     * use similar algorithm as basic matching to detect loop
     *
     * @param candidate
     * @param searchTerm
     */
    public static boolean passedLoopTest(Term candidate, Term searchTerm) {
        final ImmutableSet<Substitution> substs =
            BasicMatching.getSubstitutions(candidate, searchTerm);

        for (Substitution subst1 : substs) {
            final Substitution subst = subst1;
            if (containsLoop(subst)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Test whether this substitution constains loop. It is mainly used for unitrigger's loop test.
     */
    private static boolean containsLoop(Substitution subst) {
        final Iterator<QuantifiableVariable> it = subst.getVarMap().keyIterator();
        while (it.hasNext()) {
            if (containsLoop(subst.getVarMap(), it.next())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Code copied from logic.EqualityConstraint
     */
    private static boolean containsLoop(ImmutableMap<QuantifiableVariable, Term> varMap,
            QuantifiableVariable var) {
        ImmutableList<QuantifiableVariable> body = ImmutableSLList.nil();
        ImmutableList<Term> fringe = ImmutableSLList.nil();
        Term checkForCycle = varMap.get(var);

        if (checkForCycle.op() == var) {
            return false;
        }

        while (true) {
            for (QuantifiableVariable quantifiableVariable : checkForCycle.freeVars()) {
                final QuantifiableVariable termVar = quantifiableVariable;
                if (!body.contains(termVar)) {
                    final Term termVarterm = varMap.get(termVar);
                    if (termVarterm != null) {
                        if (termVarterm.freeVars().contains(var)) {
                            return true;
                        }
                        fringe = fringe.prepend(termVarterm);
                    }

                    if (termVar == var) {
                        return true;
                    }

                    body = body.prepend(termVar);
                }
            }

            if (fringe.isEmpty()) {
                return false;
            }

            checkForCycle = fringe.head();
            fringe = fringe.tail();
        }
    }

    boolean isElementOfMultitrigger() {
        return isElementOfMultitrigger;
    }


}
