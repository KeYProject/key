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


/**
 * A trigger consisting of a single term. Matching it against a target term yields the substitutions
 * for the quantified variables; results are cached per target term.
 */
class UniTrigger implements Trigger {

    private final Term trigger;
    /** The universal variables this trigger binds. */
    private final ImmutableSet<QuantifiableVariable> universalVariables;

    private final TriggersSet owningTriggerSet;

    /** How this trigger is matched, see {@link TriggerKind}. */
    private final TriggerKind kind;
    private final boolean isElementOfMultitrigger;

    // A TriggersSet is cached per proof (ServiceCaches.triggerSetCache) and thus shared across the
    // parallel-prover workers, so this match-result cache is hit concurrently on the cost path. The
    // exact ConcurrentLruCache is used (not the striped one): the cached substitutions are
    // expensive
    // to recompute, so the better hit rate of exact LRU eviction outweighs the trivial contention
    // on get/put. The get-then-put below stays non-atomic on purpose (the expensive matching
    // run outside the lock); at worst two workers redundantly compute the same (pure) result.
    private final ConcurrentLruCache<Term, ImmutableSet<Substitution>> matchResults =
        new ConcurrentLruCache<>(1000);
    /**
     * The results of the same matching with basic matching allowed. That matching produces
     * substitutions unification alone does not, so which of the two ran is part of what was
     * computed and
     * has to be part of the key: sharing one cache would hand the caller whichever mode happened
     * to fill the entry first. Only a generalized trigger tells the two apart, see
     * {@link #computeSubstitutionsForTerm}.
     */
    private final ConcurrentLruCache<Term, ImmutableSet<Substitution>> matchResultsByBasicMatching =
        new ConcurrentLruCache<>(1000);

    UniTrigger(Term trigger, ImmutableSet<QuantifiableVariable> universalVariables,
            TriggerKind kind, boolean isElementOfMultitrigger,
            TriggersSet owningTriggerSet) {
        this.trigger = trigger;
        this.universalVariables = universalVariables;
        this.kind = kind;
        this.isElementOfMultitrigger = isElementOfMultitrigger;
        this.owningTriggerSet = owningTriggerSet;
    }

    @Override
    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerms,
            Services services) {
        return getSubstitutionsFromTerms(targetTerms, services, true);
    }

    @Override
    public ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerms,
            Services services, boolean basicMatching) {
        ImmutableSet<Substitution> allSubs = DefaultImmutableSet.nil();
        for (Term target : targetTerms) {
            allSubs = allSubs.union(cachedSubstitutionsForTerm(target, services, basicMatching));
        }
        return allSubs;
    }

    private ImmutableSet<Substitution> cachedSubstitutionsForTerm(Term target, Services services,
            boolean basicMatching) {
        // A plain trigger is matched basically whenever it is not unified, so the mode leaves its
        // result untouched and both callers share the one cache.
        final ConcurrentLruCache<Term, ImmutableSet<Substitution>> cache =
            basicMatching && kind.isTheoryProvided() ? matchResultsByBasicMatching : matchResults;
        ImmutableSet<Substitution> subs = cache.get(target);
        if (subs == null) {
            subs = computeSubstitutionsForTerm(target, services, basicMatching);
            cache.put(target, subs);
        }
        return subs;
    }

    private ImmutableSet<Substitution> computeSubstitutionsForTerm(Term target,
            Services services, boolean basicMatching) {
        final boolean groundTarget =
            target.freeVars().isEmpty() && !(target.op() instanceof Quantifier);
        // A quantified target is unified whatever the kind: its own variables are unknowns
        // that structural matching cannot handle.
        if (!groundTarget) {
            return Matching.twoSidedMatching(this, target, services);
        }
        // Against a ground target the kind decides. Only structural matching lets a theory
        // solve an array index: unification decides a pair of terms as a whole and offers no
        // point at which a failing index could be solved.
        switch (kind) {
            case PATTERN:
                return Matching.basicMatching(this, target, services);
            case GENERALIZED:
                ImmutableSet<Substitution> subs = Matching.twoSidedMatching(this, target, services);
                if (basicMatching) {
                    final ImmutableSet<Substitution> basicSubs =
                        Matching.basicMatching(this, target, services);
                    if (!basicSubs.isEmpty()) {
                        subs = subs.union(basicSubs);
                    }
                }
                return subs;
            case GENERALIZED_UNIFY:
                return Matching.twoSidedMatching(this, target, services);
            case NEEDS_UNIFY:
            default:
                return DefaultImmutableSet.nil();
        }
    }


    @Override
    public boolean isTheoryProvided() {
        return kind.isTheoryProvided();
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
            BasicMatching.getSyntacticSubstitutions(candidate, searchTerm);

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
     * {@code var} is reached again -- i.e. whether its definition is cyclic.
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
