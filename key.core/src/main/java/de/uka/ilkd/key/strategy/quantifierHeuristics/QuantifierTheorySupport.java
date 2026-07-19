/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Junctor;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSet;

/**
 * A theory's contribution to quantifier instantiation.
 *
 * The instantiation heuristic needs knowledge that is specific to each theory at two points. When
 * choosing triggers: what counts as coordinate or connective material rather than a meaningful
 * observation (an array index, an integer comparison), and which derived triggers make an
 * observation matchable against the terms a proof actually produces (a read generalized over the
 * heaps of a symbolic execution). And when predicting the cost of an instantiation: whether a
 * literal is proved true or false, from itself or from an assumed literal, by the theory's own
 * reasoning (arithmetic comparisons, equality up to renaming). This interface isolates that
 * knowledge. Registering a new support in {@link TriggersSet#THEORY_SUPPORTS} is the only change
 * needed to teach the heuristic about a further theory; {@link TriggersSet} and
 * {@link PredictCostProver} stay untouched.
 */
interface QuantifierTheorySupport {

    /** The outcome of judging a literal for cost prediction. */
    enum LiteralDecision {
        PROVED, REFUTED, UNKNOWN;

        /**
         * @return the decision for the negation of the judged literal
         */
        LiteralDecision negate() {
            return switch (this) {
                case PROVED -> REFUTED;
                case REFUTED -> PROVED;
                case UNKNOWN -> UNKNOWN;
            };
        }
    }

    /**
     * Maps a truth term, as the theory reasoning returns it, to a decision: the true constant is
     * {@link LiteralDecision#PROVED}, the false constant {@link LiteralDecision#REFUTED}, and any
     * other term (an undecided literal) {@link LiteralDecision#UNKNOWN}.
     *
     * @param t a truth term
     * @return the matching decision
     */
    static LiteralDecision fromTruthTerm(JTerm t) {
        if (t.op() == Junctor.TRUE) {
            return LiteralDecision.PROVED;
        }
        if (t.op() == Junctor.FALSE) {
            return LiteralDecision.REFUTED;
        }
        return LiteralDecision.UNKNOWN;
    }

    /**
     * Whether {@code candidate} must not be used as a standalone trigger, because for this theory
     * it is coordinate or connective material rather than a meaningful observation.
     *
     * @param candidate a subterm that contains the quantified variables and is a trigger candidate
     * @param services access to the theory operators
     */
    boolean rejectsAsTrigger(JTerm candidate, Services services);

    /**
     * Additional triggers derived from the accepted trigger {@code term}, for example a read
     * generalized so it matches across the many heaps of a proof. The returned triggers are matched
     * by unification (they may contain metavariables).
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the theory operators
     * @return derived triggers, possibly empty
     */
    List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services);

    /**
     * Checks whether the literal holds on its own, for cost prediction. The literal is passed
     * already stripped of its leading negations; the caller re-applies them to the returned
     * decision, so an implementation reasons about the positive form only.
     *
     * @param strippedLiteral a literal without leading negations
     * @param services access to the theory operators
     * @return whether this theory proves the literal true, false, or cannot decide it
     */
    default LiteralDecision decideStrippedSelf(JTerm strippedLiteral, Services services) {
        return LiteralDecision.UNKNOWN;
    }

    /**
     * Checks whether the literal follows from an assumed-true {@code axiom}, for cost prediction.
     * Leading negations of both the literal and the axiom are handled by the implementation.
     *
     * @param literal a literal to decide
     * @param axiom a literal assumed to be true
     * @param services access to the theory operators
     * @return whether the axiom proves the literal true, false, or cannot decide it
     */
    default LiteralDecision decideFromAxiom(JTerm literal, JTerm axiom, Services services) {
        return LiteralDecision.UNKNOWN;
    }

    /**
     * Whether the equality-based normalisation of the cost prediction (see {@link Congruence}) may
     * rewrite occurrences of {@code from} to {@code to}, justified by an assumed equality between
     * the two. The proof search keeps the terms of a theory in a normal form of the theory's own
     * rules, integer terms in polynomial form for example. A theory vetoes here when the rewrite
     * would replace such a normal form, so the decisions of {@link #decideStrippedSelf} and
     * {@link #decideFromAxiom} still see the forms they understand. When a rewrite is vetoed the
     * congruence tries the opposite direction, and leaves the equality out entirely if that is
     * vetoed too.
     *
     * @param from the term whose occurrences would be rewritten
     * @param to the replacement term
     * @param services access to the theory operators
     * @return whether this theory permits the rewrite
     */
    default boolean allowsEqualityRewrite(JTerm from, JTerm to, Services services) {
        return true;
    }
}
