/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Collection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;

/**
 * The within-band ordering of tied quantifier instantiation candidates.
 *
 * When several candidates share the predicted instantiation cost, the primary prediction cannot
 * separate them, and the choice would otherwise fall to the position of the quantified formula on
 * the sequent. A tie-break orders the band by content instead. Which content signal is used is a
 * strategy: {@link PolarityTieBreak} orders by how strongly an instance is connected to the
 * proving-polarity parts of the sequent, {@link GenPolTieBreak} orders by how late the instance's
 * newest skolem constant was introduced on the branch, breaking a same-generation tie by the
 * polarity connection.
 *
 * A strategy runs in two phases: {@link #prepare} computes the facts shared by all candidates of
 * one quantified formula once and returns a {@link Scorer}; the scorer then answers each candidate.
 * The tie-break value stays far below the distance of the scaled cost bands (see
 * {@link de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCostScalerFeature}), so the
 * prediction itself is never overridden.
 */
interface QuantifierInstantiationTieBreak {

    /**
     * The read-only view of a quantified formula's instantiation the tie-break reads: the candidate
     * instances, the sequent they were collected from, the goal for the branch history, and access
     * to the theory operators and caches.
     *
     * @param candidates the candidate instances
     * @param sequent the sequent
     * @param goal the goal
     * @param services the services
     */
    record View(Collection<Term> candidates, Sequent sequent, Goal goal, Services services) {
    }

    /**
     * Prepares the shared facts for the candidates of one quantified formula.
     *
     * @param view the instantiation view
     * @return a scorer for the view's candidates
     */
    Scorer prepare(View view);

    /** Scores a single candidate, using the facts prepared for its quantified formula. */
    @FunctionalInterface
    interface Scorer {
        /**
         * @param instance a candidate instance
         * @return its tie-break cost, small compared to the scaled cost bands
         */
        long tieBreak(Term instance);
    }
}
