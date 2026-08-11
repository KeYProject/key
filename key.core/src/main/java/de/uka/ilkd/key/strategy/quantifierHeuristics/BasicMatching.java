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

/**
 * Matches a trigger against a ground term of the sequent by descending both in step, binding a
 * quantified variable to whatever ground subterm stands at its position. Operators and arities
 * have to agree at every position above the variables, so the trigger's structure is fixed and
 * only the variables are open. The trigger {@code select(heap, a, arr(i))} with quantified
 * {@code i} matches the sequent term {@code select(heap, a, arr(3))} and binds {@code i} to
 * {@code 3}; it does not match {@code select(heap2, a, arr(3))}, whose heap differs, nor
 * {@code select(heap, b, arr(3))}.
 *
 * This is the weaker of the two matchings the heuristic uses. Unification (see
 * {@link TwoSidedMatching}) binds metavariables on the trigger's side as well, so the trigger
 * {@code select(H, a, arr(i))}, whose metavariable {@code H} stands for any heap, matches
 * {@code select(heap2, a, arr(3))}, which basic matching cannot do. What unification does not
 * offer is a place to intervene: it answers for the two terms at once and does not report which
 * pair of subterms defeated it. Basic matching descends position by position with the ground term
 * fixed, so a failing comparison stays located at the position where it failed and can be handed
 * to a theory there: where {@code arr(base + i)} meets {@code arr(x)} the integer theory solves
 * {@code base + i = x} for {@code i} (see {@link QuantifierTheorySupport#solveForVariable}) and
 * the match continues with {@code i = x - base}.
 */
class BasicMatching {

    private BasicMatching() {}

    /**
     * Matches <code>trigger</code> against <code>targetTerm</code> and its subterms, comparing
     * the two structures alone.
     *
     * @param trigger a uni-trigger
     * @param targetTerm a ground term
     * @return all substitutions found
     */
    static ImmutableSet<Substitution> getSyntacticSubstitutions(Term trigger, Term targetTerm) {
        return getSubstitutions(trigger, targetTerm, null);
    }

    /**
     * As above, and where a comparison fails the theories are asked whether they can solve it.
     *
     * @param trigger a uni-trigger
     * @param targetTerm a ground term
     * @param services the theories' operators, or null to compare the structures alone
     * @return all substitutions found
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
        final Bindings bindings =
            matchRec(Bindings.EMPTY, pattern, instance, services, false);
        if (bindings == null) {
            return null;
        }
        return new Substitution(bindings.variables(), bindings.solvedArrayIndex());
    }

    /**
     * What a match has bound so far. Only {@code variables} is the result. A metavariable may
     * occur at more than one position of a trigger and has to stand for the same term at each,
     * which is what {@code metavariables} checks; it is dropped when the match ends.
     *
     * @param variables the instantiation of the trigger's quantified variables
     * @param metavariables the terms the trigger's metavariables stand for
     */
    private record Bindings(ImmutableMap<QuantifiableVariable, Term> variables,
            ImmutableMap<Metavariable, Term> metavariables, boolean solvedArrayIndex) {

        static final Bindings EMPTY = new Bindings(DefaultImmutableMap.nilMap(),
            DefaultImmutableMap.nilMap(), false);

        Bindings withVariable(QuantifiableVariable var, Term instance) {
            final Term bound = variables.get(var);
            if (bound == null) {
                return new Bindings(variables.put(var, instance), metavariables, solvedArrayIndex);
            }
            return bound.equals(instance) ? this : null;
        }

        Bindings withMetavariable(Metavariable metavariable, Term instance) {
            final Term bound = metavariables.get(metavariable);
            if (bound == null) {
                return new Bindings(variables, metavariables.put(metavariable, instance),
                    solvedArrayIndex);
            }
            return bound.equals(instance) ? this : null;
        }

        Bindings withSolution(ImmutableMap<QuantifiableVariable, Term> solved) {
            return new Bindings(solved, metavariables, true);
        }
    }

    /**
     * match the pattern to instance recursively.
     */
    private static Bindings matchRec(Bindings bindings, Term pattern, Term instance,
            Services services, boolean nested) {
        final var patternOp = pattern.op();

        if (patternOp instanceof QuantifiableVariable var) {
            return bindings.withVariable(var, instance);
        }

        // A metavariable stands for any term of its sort, so comparing it as a rigid symbol fails
        // against every concrete heap. Bind it like a variable instead, but only when matching for
        // instantiation: trigger selection matches too, and binding there would change which
        // candidates become triggers.
        if (services != null && patternOp instanceof Metavariable metavariable
                && pattern.sort() == instance.sort()) {
            return bindings.withMetavariable(metavariable, instance);
        }

        if (patternOp != instance.op()) {
            // Only below a read that has matched so far. Solving a bare array index against an
            // arbitrary integer says nothing until the read around it is known to be the same.
            return nested ? solveByTheory(bindings, pattern, instance, services) : null;
        }
        for (int i = 0; i < pattern.arity(); i++) {
            final Bindings matched =
                matchRec(bindings, pattern.sub(i), instance.sub(i), services, true);
            if (matched == null) {
                // The operators agree at the top and disagree below, which is what an array index
                // written against a different offset looks like: both sides are sums, but their
                // parts do not line up. Solving the two as one equation still succeeds.
                return nested ? solveByTheory(bindings, pattern, instance, services) : null;
            }
            bindings = matched;
        }
        return bindings;
    }

    /**
     * Last resort when the structures disagree: ask the theories to solve the pattern for one of
     * its variables. An array index written against an offset never matches an absolute one, so
     * without this a fact about {@code base + t} cannot be used on a term about {@code x}.
     */
    private static Bindings solveByTheory(Bindings bindings, Term pattern, Term instance,
            Services services) {
        // No services means the caller asked to compare the structures alone.
        if (services == null || !(pattern instanceof JTerm patternTerm)
                || !(instance instanceof JTerm instanceTerm)) {
            return null;
        }
        for (QuantifierTheorySupport support : TriggersSet.THEORY_SUPPORTS) {
            final ImmutableMap<QuantifiableVariable, Term> solved = support
                    .solveForVariable(patternTerm, instanceTerm, bindings.variables(), services);
            if (solved != null) {
                return bindings.withSolution(solved);
            }
        }
        return null;
    }



}
