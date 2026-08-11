/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.UpdateApplication;

import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableSet;

class BasicMatching {

    private BasicMatching() {}

    /**
     * matching <code>trigger</code> to <code>targetTerm</code> recursively
     *
     * @param trigger a uni-trigger
     * @param targetTerm a gound term
     * @return all substitution found from this matching
     */
    static ImmutableSet<Substitution> getSubstitutions(Term trigger, Term targetTerm) {
        return getSubstitutions(trigger, targetTerm, null);
    }

    /**
     * As above, but with the theory supports consulted where syntactic matching fails. Passing no
     * services keeps the match purely syntactic, which is what the trigger loop test wants.
     */
    static ImmutableSet<Substitution> getSubstitutions(Term trigger, Term targetTerm,
            Services services) {
        ImmutableSet<Substitution> allsubs = DefaultImmutableSet.nil();
        if (targetTerm.freeVars().size() > 0 || targetTerm.op() instanceof Quantifier) {
            return allsubs;
        }
        final Substitution subst = match(trigger, targetTerm, services);
        if (subst != null) {
            allsubs = allsubs.add(subst);
        }
        final var op = targetTerm.op();
        if (!(op instanceof JModality || op instanceof UpdateApplication)) {
            for (int i = 0; i < targetTerm.arity(); i++) {
                allsubs = allsubs.union(getSubstitutions(trigger, targetTerm.sub(i), services));
            }
        }
        return allsubs;
    }

    /**
     * @param pattern
     * @param instance
     * @return all substitution that a given pattern(ex: a term of a uniTrigger) match in the
     *         instance.
     */
    private static Substitution match(Term pattern, Term instance, Services services) {
        final ImmutableMap<QuantifiableVariable, Term> map =
            matchRec(DefaultImmutableMap.nilMap(), pattern, instance, services, false);
        if (map == null) {
            return null;
        }
        return new Substitution(map);
    }

    /**
     * match the pattern to instance recursively.
     */
    private static ImmutableMap<QuantifiableVariable, Term> matchRec(
            ImmutableMap<QuantifiableVariable, Term> varMap, Term pattern, Term instance,
            Services services, boolean nested) {
        final var patternOp = pattern.op();

        if (patternOp instanceof QuantifiableVariable) {
            return mapVarWithCheck(varMap, (QuantifiableVariable) patternOp, instance);
        }

        if (patternOp != instance.op()) {
            // Only inside an observation that has matched so far. Solving a bare coordinate
            // against an arbitrary integer of the sequent says nothing: the shift is meaningful
            // only once the read around it is known to be the same read.
            return nested ? solveByTheory(varMap, pattern, instance, services) : null;
        }
        for (int i = 0; i < pattern.arity(); i++) {
            final ImmutableMap<QuantifiableVariable, Term> matched =
                matchRec(varMap, pattern.sub(i), instance.sub(i), services, true);
            if (matched == null) {
                // Shapes agree at the top and disagree below, which is what a coordinate written
                // against a different offset looks like: both sides are sums, but their parts do
                // not line up. Solving the two as one equation still succeeds.
                return nested ? solveByTheory(varMap, pattern, instance, services) : null;
            }
            varMap = matched;
        }
        return varMap;
    }

    /**
     * Last resort when the shapes disagree: ask the theories whether the pattern can be solved for
     * one of its variables. A coordinate written relative to an offset never matches an absolute
     * one by shape, so without this a fact stated over {@code base + t} is unreachable from a term
     * about {@code x}.
     */
    private static ImmutableMap<QuantifiableVariable, Term> solveByTheory(
            ImmutableMap<QuantifiableVariable, Term> varMap, Term pattern, Term instance,
            Services services) {
        if (services == null || !(pattern instanceof JTerm patternTerm)
                || !(instance instanceof JTerm instanceTerm)) {
            return null;
        }
        for (QuantifierTheorySupport support : TriggersSet.THEORY_SUPPORTS) {
            final ImmutableMap<QuantifiableVariable, Term> solved =
                support.solveForVariable(patternTerm, instanceTerm, varMap, services);
            if (solved != null) {
                return solved;
            }
        }
        return null;
    }

    /**
     * match a variable to a instance.
     *
     * @return true if it is a new vaiable or the instance it matched is the same as that it matched
     *         before.
     */
    private static ImmutableMap<QuantifiableVariable, Term> mapVarWithCheck(
            ImmutableMap<QuantifiableVariable, Term> varMap, QuantifiableVariable var,
            Term instance) {
        final Term oldTerm = varMap.get(var);
        if (oldTerm == null) {
            return varMap.put(var, instance);
        }

        if (oldTerm.equals(instance)) {
            return varMap;
        }
        return null;
    }


}
