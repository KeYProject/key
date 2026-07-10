/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/*
 * Theory-internal cost constants for the JavaCardDL strategy, grouped per sub-area
 * (Integer-style, one file per theory): JavaCardDLCost for the axiom / observer /
 * comprehension / induction reasoning, HeapSelectCost for the pull-out-select pipeline
 * (a future component strategy of its own; it is kept as a separate holder to pre-stage
 * that split and moves with it).
 */

/**
 * JavaCardDL-theory-internal ordering costs, used by {@link JavaCardDLStrategy} (the axiom /
 * observer / comprehension / induction reasoning; the heap/select pipeline has its own
 * {@link HeapSelectCost}).
 *
 * <p>
 * Values are byte-identical to the literals they replace. Names are chosen by <em>meaning</em>, not
 * by numeric coincidence with a {@link org.key_project.prover.strategy.costbased.CostBand} tier —
 * e.g. {@link #AUTO_INDUCTION} shares −6500 with the FOL type-hierarchy rule but is not type
 * reasoning, and {@link #JAVA_INTEGER_SEMANTICS} / {@link #COMPREHENSION_SIMPLIFY} share −5000 with
 * NORMALIZE but are a definitional expansion / a simplify-like step. Verify changes with a full
 * runAllProofs.
 * </p>
 */
final class JavaCardDLCost {
    private JavaCardDLCost() {}

    /**
     * Insert the java integer operator definitions ({@code javaIntegerSemantics}) once no program
     * is left / on a single branch: a definitional expansion, not a canonicalization.
     */
    static final long JAVA_INTEGER_SEMANTICS = -5000;

    /** Loc-set CNF commutation ({@code cnf_setComm}). */
    static final long LOCSET_CNF_COMMUTE = -800;

    /** Apply a class axiom ({@code classAxiom}). */
    static final long CLASS_AXIOM = -250;

    /** {@code inReachableStateImplication}. */
    static final long IN_REACHABLE_STATE = 100;

    /**
     * Limit an observer symbol ({@code limitObserver}); must have better priority than classAxiom.
     */
    static final long LIMIT_OBSERVER = -200;

    /** Dependency-contract application ({@code UseDependencyContractRule} / dependency feature). */
    static final long DEPENDENCY_CONTRACT = 250;

    // Comprehensions form a simplify/enlarge-style pair (cf. simplify / simplify_ENLARGING). The
    // ENLARGE band doc even names "comprehension / map unfolding" — a step-3 candidate to normalize
    // COMPREHENSION_SIMPLIFY -> SIMPLIFY and COMPREHENSION_ENLARGE -> ENLARGE. Byte-identical here.
    /** Ordinary comprehension handling ({@code comprehensions}). */
    static final long COMPREHENSION = -50;
    /** Cheap, simplify-like comprehension application ({@code comprehensions_low_costs}). */
    static final long COMPREHENSION_SIMPLIFY = -5000;
    /** Expensive, enlarge-like comprehension application ({@code comprehensions_high_costs}). */
    static final long COMPREHENSION_ENLARGE = 10000;

    /**
     * Auto-induction ({@code auto_induction}); must be applied like a delta rule. NOT the TYPE band
     * despite sharing −6500 with the FOL type-hierarchy rule.
     */
    static final long AUTO_INDUCTION = -6500;

    /**
     * Auto-induction lemma ({@code auto_induction_lemma}); a beta rule with higher-than-usual
     * priority.
     */
    static final long AUTO_INDUCTION_LEMMA = -300;

    /** User taclets set to low priority: applied late. */
    static final long USER_TACLET_LOW_PRIORITY = 10000;

    /** User taclets set to high priority: mildly preferred. */
    static final long USER_TACLET_HIGH_PRIORITY = -50;
}


/**
 * Costs of the pull-out-select heap simplification pipeline, used by {@link JavaCardDLStrategy}.
 * This is the coherent heap/select cluster that is a candidate to be promoted into its own
 * component strategy later; it is kept in a dedicated holder to pre-stage that split.
 *
 * <p>
 * <b>Combination-relevant, not purely local:</b> this ladder is tuned <em>relative to</em> the
 * demodulation cost {@link CombinationCost#ORDERED_REWRITING}: {@link #APPLY_SELECT_EQ} is the
 * JavaCardDL-side remainder of the tuned sum {@link CombinationCost#APPLY_SELECT_EQ_EFFECTIVE}
 * (the {@code applyEq} taclet carries both rule sets, so the dispatch sums the contributions).
 * </p>
 *
 * <p>
 * Values are byte-identical to the literals they replace; verify changes with a full runAllProofs
 * (as for {@link org.key_project.prover.strategy.costbased.CostBand}).
 * </p>
 */
final class HeapSelectCost {
    private HeapSelectCost() {}

    /** {@code pull_out_select} when the focus select sits below an update (pull it out harder). */
    static final long PULL_OUT_SELECT_BELOW_UPDATE = -4200;

    /** {@code pull_out_select} otherwise. */
    static final long PULL_OUT_SELECT = -1900;

    /**
     * {@code apply_select_eq}: replace a not-yet-simplified select by the skolem constant of its
     * pull-out. The {@code applyEq} taclet carries both {@code apply_equations} and
     * {@code apply_select_eq}, so the effective cost is the SUM of the two bindings; the tuned
     * quantity is {@link CombinationCost#APPLY_SELECT_EQ_EFFECTIVE} and this constant is the
     * JavaCardDL-side remainder (currently −1700).
     */
    static final long APPLY_SELECT_EQ =
        CombinationCost.APPLY_SELECT_EQ_EFFECTIVE - CombinationCost.ORDERED_REWRITING;

    /** {@code simplify_select}: simplify the select term in the pulled-out equation. */
    static final long SIMPLIFY_SELECT = -5600;

    /** {@code apply_auxiliary_eq}: replace the skolem constant by its computed value. */
    static final long APPLY_AUXILIARY_EQ = -5500;

    /** {@code hide_auxiliary_eq}: hide the auxiliary equation once the constant is replaced. */
    static final long HIDE_AUXILIARY_EQ = -5400;

    /** {@code hide_auxiliary_eq_const}: same, for the constant-valued case. */
    static final long HIDE_AUXILIARY_EQ_CONST = -500;
}
