/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.strategy.quantifierHeuristics.TriggersSet;
import de.uka.ilkd.key.strategy.quantifierHeuristics.constraint.Metavariable;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

/**
 * A theory's contribution to the choice of what a quantified formula is instantiated with.
 *
 * Which subterms make a usable trigger depends on the theory a term belongs to: an array index or
 * an integer comparison matches everywhere and discriminates nothing, while a read determines
 * which location is accessed.
 * A theory also derives further triggers from an accepted one, for example a read generalized so
 * it matches over the many heaps of a proof, and it names instances that no trigger reaches at
 * all.
 *
 * This is the part of a theory's contribution that is specific to the terms a front end builds.
 * A front end without a heap has nothing to contribute here and still reuses
 * {@link TheoryReasoning}.
 */
public interface TriggerSupport {

    /**
     * The verdict of a theory on a trigger candidate: whether the candidate becomes a trigger,
     * and whether the search for triggers continues with the term enclosing it.
     *
     * Trigger selection traverses each literal of the quantified formula bottom-up. A candidate
     * is a subterm that contains a quantified variable and is not a variable itself. For every
     * candidate the verdict of every theory is determined, and the verdicts are combined as
     * follows: one {@code FORBIDDEN} discards the candidate; otherwise one
     * {@code PREFER_ENCLOSING} registers the candidate as a trigger and continues the search
     * with the enclosing term; otherwise the candidate is registered as a trigger, and an
     * enclosing term becomes a candidate only if it contains a quantified variable that the
     * registered trigger does not.
     */
    enum CandidateVerdict {
        /**
         * The candidate may become a trigger. If every theory returns {@code ACCEPTABLE}, the
         * candidate is registered, and no enclosing term becomes a trigger for the variables
         * the candidate binds.
         */
        ACCEPTABLE,
        /**
         * The candidate is not a trigger, because a match of it discriminates nothing: an
         * equality or a comparison {@code <=}, {@code >=} matches every literal of its shape,
         * and the index packaging {@code arr(i)} of an array access matches every access. The
         * search continues with the enclosing term. Where every subterm of a term is forbidden,
         * the term itself is the candidate.
         */
        FORBIDDEN,
        /**
         * The candidate is a trigger, and the term enclosing it is a candidate as well. The
         * index {@code k + t} of an array access {@code a[k + t]} is such a case. The sum binds
         * {@code t} but does not determine the array. The read determines the array, so both
         * are registered.
         */
        PREFER_ENCLOSING
    }

    /**
     * Returns this theory's verdict on a trigger candidate. The combination of the verdicts of
     * all theories is described at {@link CandidateVerdict}.
     *
     * @param candidate a subterm that contains the quantified variables and is a trigger candidate
     * @param enclosing the term the candidate is an argument of, null at the top of a literal
     * @param services access to the theory operators
     * @return the verdict
     */
    CandidateVerdict verdictOn(JTerm candidate, JTerm enclosing, Services services);

    /**
     * Additional triggers derived from the accepted trigger {@code term}, for example a read
     * generalized so it matches across the many heaps of a proof. The returned triggers are matched
     * by unification (they may contain metavariables).
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the theory operators
     * @param metavariableFactory supplies the metavariables a derived trigger needs
     * @return derived triggers, possibly empty
     */
    List<JTerm> provideTriggers(JTerm term, ImmutableSet<QuantifiableVariable> clauseVariables,
            Services services, MetavariableFactory metavariableFactory);

    /**
     * The fallback triggers this theory offers for a clause of a formula that no trigger
     * instantiates.
     *
     * Some formulas yield no covering trigger in any clause: every literal holding the
     * quantified variable is forbidden, and what remains binds no universal variable. Such a
     * formula is never instantiated through its own terms. This method is the last resort, asked
     * for each clause of such a formula and for no other, so an implementation does not compete
     * with the ordinary selection and cannot lose an instantiation that exists anyway. The
     * given clause is therefore uncovered itself; the value also tells, per literal, what the
     * selection did find. Instances a theory reads off the formula directly, without a trigger,
     * are not part of this condition: they are found later, per sequent.
     *
     * A returned trigger is registered as theory-provided: it is unified, and under the most
     * informed treatment also matched structurally, so a metavariable in it can bind a term that
     * does not occur in the formula, and a theory can solve an index below it. Instances it
     * yields carry the {@code FALLBACK} origin, which only the most informed treatment admits. A
     * fallback that binds only some of the clause's variables is an element, and may combine
     * with other elements, the formula's own included, into a covering multi-trigger: the cover
     * search runs again after the fallbacks are registered.
     *
     * @param selection one clause of the formula, with the triggers its literals yielded
     * @param services access to the theory operators
     * @param metavariableFactory supplies the metavariables a fallback trigger needs
     * @return the fallback triggers, possibly empty
     */
    default List<JTerm> fallbackTriggers(ClauseTriggers selection, Services services,
            MetavariableFactory metavariableFactory) {
        return List.of();
    }

    /**
     * The instance candidates this theory supplies for a subterm of the quantified formula. They
     * are used for the quantified variable directly, not through a trigger.
     *
     * Matching binds the quantified variable to a subterm of the term it matched, so it cannot
     * produce an instance that occurs in no trigger position. Such an instance has to come from a
     * theory instead. An array read is one case: the index a store writes is what collapses the
     * read, and it is ground, so no trigger contains it.
     *
     * The caller descends through the matrix and passes every subterm, so an implementation
     * decides on the subterm alone. A candidate is costed like a matched one.
     *
     * @param subterm a subterm of the quantified formula's matrix
     * @param variable the quantified variable an instance is sought for
     * @param services access to the theory operators
     * @return the candidate instances, possibly empty
     */
    default List<JTerm> provideInstances(JTerm subterm, QuantifiableVariable variable,
            Services services) {
        return List.of();
    }

    /**
     * Hands out the metavariables a derived trigger puts in place of a ground subterm.
     *
     * The names are counted within one {@link TriggersSet}, which is built from the quantified
     * formula alone, so the same formula always yields the same names and no two derived triggers
     * share one. That matters because two metavariables of equal name are still distinct and are
     * then ordered by a creation counter shared across the whole prover, which would make the
     * order, and through it the instances chosen, depend on which goal built its trigger set
     * first. A support must therefore take its metavariables from here rather than name them.
     */
    interface MetavariableFactory {
        /**
         * @param sort the sort the metavariable stands for
         * @return a metavariable distinct from every other one of its trigger set
         */
        Metavariable fresh(Sort sort);
    }
}
