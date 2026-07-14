/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * FOL-theory-internal ordering costs, used by {@link FOLStrategy}. These are the fine, within-FOL
 * ordering values that are <em>reused</em> across FOLStrategy's normalisation / splitting /
 * equation methods and therefore deserve a name of their own; genuinely one-off nudges are written
 * directly as {@code CostBand.<band>.at(delta)} at the call site instead.
 *
 * <p>
 * Values are byte-identical to the literals they replace. They position FOL rules within the shared
 * {@link org.key_project.prover.strategy.costbased.CostBand} ladder, so changing one shifts the
 * cross-theory search — verify with a full runAllProofs and a Model-Search node-for-node comparison
 * (as for {@code CostBand}).
 * </p>
 */
final class FOLCost {
    private FOLCost() {}

    /**
     * Distribution / swapping of quantifiers ({@code distrQuantifier}, {@code swapQuantifiers}).
     */
    static final long QUANTIFIER_DISTRIBUTION = -300;

    /**
     * Restructuring of CNF clauses by associativity / distribution ({@code cnf_orAssoc},
     * {@code cnf_andAssoc}, {@code cnf_dist}); the small {@code ± delta} at the call sites orders
     * these among themselves. These are the fine deltas summed on top of the
     * {@link CombinationCost#CNF_CONVERSION} level via the dual rule-set tags of the
     * {@code conjNormalForm} taclets.
     */
    static final long CNF_RESTRUCTURE = -35;

    /**
     * Defer {@code replace_known_right} when its target is in the consequent of an implication or
     * inside an equivalence, so the connective is decomposed first (which makes the antecedent
     * available as a known-true fact). Deliberately <em>not</em> applied to
     * {@code replace_known_left}, whose antecedent-true facts stay valid across the decomposition.
     */
    static final long REPLACE_KNOWN_UNDER_CONNECTIVE = 100;

    /** Standard cost of a direct cut ({@code cut_direct}). */
    static final long CUT_DIRECT_STANDARD = 100;

    /** Preferred direction of the {@code pullOutQuantifier*} rules. */
    static final long PULL_OUT_QUANTIFIER = -20;

    /** Dispreferred direction of the {@code pullOutQuantifier*} rules. */
    static final long PULL_OUT_QUANTIFIER_REVERSE = -40;
}
