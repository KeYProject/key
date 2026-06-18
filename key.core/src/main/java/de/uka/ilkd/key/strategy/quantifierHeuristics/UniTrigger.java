/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Quantifier;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;


class UniTrigger implements Trigger {

    private final Term trigger;
    private final ImmutableSet<QuantifiableVariable> uqvs;

    private final TriggersSet triggerSetThisBelongsTo;

    private final boolean onlyUnify;
    private final boolean isElementOfMultitrigger;

    // A TriggersSet is cached per proof (ServiceCaches.triggerSetCache) and thus shared across the
    // parallel-prover workers, so this match-result cache is hit concurrently on the cost path. The
    // exact ConcurrentLruCache is used (not the striped one): the cached substitutions are
    // expensive
    // to recompute, so the better hit rate of exact LRU eviction outweighs the trivial contention
    // on
    // get/put. The get-then-put below stays non-atomic on purpose (the expensive matching runs
    // outside the lock); at worst two workers redundantly compute the same (pure) result.
    private final ConcurrentLruCache<Term, ImmutableSet<Substitution>> matchResults =
        new ConcurrentLruCache<>(1000);

    UniTrigger(Term trigger, ImmutableSet<QuantifiableVariable> uqvs, boolean isUnify,
            boolean isElementOfMultitrigger, TriggersSet triggerSetThisBelongsTo) {
        this.trigger = trigger;
        this.uqvs = uqvs;
        this.onlyUnify = isUnify;
        this.isElementOfMultitrigger = isElementOfMultitrigger;
        this.triggerSetThisBelongsTo = triggerSetThisBelongsTo;
    }

    @Override
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


    @Override
    public Term getTriggerTerm() {
        return trigger;
    }

    public boolean equals(Object arg0) {
        if (!(arg0 instanceof UniTrigger a)) {
            return false;
        }
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
        final var it = subst.getVarMap().keyIterator();
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
    private static boolean containsLoop(
            ImmutableMap<QuantifiableVariable, Term> varMap,
            QuantifiableVariable var) {
        ImmutableList<QuantifiableVariable> body = ImmutableList.nil();
        ImmutableList<Term> fringe = ImmutableList.nil();
        Term checkForCycle = varMap.get(var);

        if (checkForCycle.op() == var) {
            return false;
        }

        while (true) {
            for (var quantifiableVariable : checkForCycle.freeVars()) {
                final QuantifiableVariable termVar = quantifiableVariable;
                if (!body.contains(termVar)) {
                    final var termVarterm = (JTerm) varMap.get(termVar);
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
