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
     * A theory's verdict on one trigger candidate, see {@link #verdictOn}.
     */
    enum CandidateVerdict {
        /** The candidate may become a trigger. */
        ACCEPTABLE,
        /**
         * The candidate is never a trigger, because for this theory it discriminates nothing:
         * a connective, or a wrapper that adds no information to its content and its enclosing
         * term.
         * It does not block the term enclosing it: where every subterm of a term is forbidden,
         * the term itself is the candidate.
         */
        FORBIDDEN,
        /**
         * The candidate is a trigger, but the search for triggers continues into the term
         * enclosing it. An array access's index expression is the case at hand: it is a usable
         * trigger, yet only the read around it determines the accessed array, so the read must
         * become a trigger too.
         */
        PREFER_ENCLOSING
    }

    /**
     * This theory's verdict on a trigger candidate at its position.
     *
     * The selection walks the formula and asks every theory at every candidate. A single
     * {@code FORBIDDEN} discards the candidate; otherwise a single {@code PREFER_ENCLOSING}
     * keeps the search going past it.
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
     * The fallback triggers this theory offers for a clause that has no covering trigger.
     *
     * Some clauses yield no covering trigger: every literal holding the quantified variable is
     * forbidden, and what remains binds no universal variable. Such a clause is never
     * instantiated through its own terms. This method is the last resort, asked only for such a
     * clause, so an implementation does not compete with the ordinary selection and cannot lose
     * an instantiation that exists anyway. It receives what the selection did find, per literal,
     * so it can address the literals that yielded nothing.
     *
     * A returned trigger is registered as theory-provided: it is unified, and under the most
     * informed treatment also matched structurally, so a metavariable in it can bind a term the
     * that does not occur in the formula, and a theory can solve an index below it. Instances it
     * yields carry
     * the {@code FALLBACK} origin, which only the most informed treatment admits. A fallback
     * that covers only part of the clause's variables joins no multi-trigger cover; the covers
     * are built before the fallbacks are asked for.
     *
     * @param selection the clause and the triggers its literals yielded
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
