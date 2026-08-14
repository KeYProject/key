/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableSet;

/**
 * A theory's contribution to the choice of what a quantified formula is instantiated with.
 *
 * Which subterms make a usable trigger depends on the theory a term belongs to: an array index or
 * an integer comparison matches everywhere and says nothing, a read says which access is meant.
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
     * Whether {@code candidate} must not be used as a standalone trigger, because for this theory
     * it is an array index or a connective rather than a read.
     *
     * @param candidate a subterm that contains the quantified variables and is a trigger candidate
     * @param services access to the theory operators
     */
    boolean rejectsAsTrigger(JTerm candidate, Services services);

    /**
     * Whether a candidate should give way to the term enclosing it, when that term yields a
     * trigger of its own.
     *
     * Unlike {@link #rejectsAsTrigger}, this is a preference and not a veto. An array index
     * matches every integer term on the sequent, while the read around it says which access is
     * meant. Where no enclosing term yields a trigger the candidate is used anyway, since a
     * clause without a trigger is never instantiated.
     *
     * @param candidate a trigger candidate
     * @param enclosing the term the candidate is an argument of, null at the top of a literal
     * @param services access to the theory's operators
     * @return whether an enclosing trigger is preferable to this candidate
     */
    default boolean prefersEnclosingTrigger(JTerm candidate, JTerm enclosing, Services services) {
        return false;
    }

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
