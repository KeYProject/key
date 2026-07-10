/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

import org.key_project.prover.strategy.costbased.feature.ConstFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * The shared, cross-theory priority ladder for the cost-based strategies.
 *
 * <p>
 * Rule costs from every component strategy (theory) are summed per rule and the globally
 * cheapest applicable rule is applied, so a band's <em>absolute</em> value fixes its priority
 * against <em>every other theory</em> — in practice the theories interleave at almost every
 * step. A band is therefore combination-relevant. The fine ordering of rules <em>within</em> a
 * band is expressed as {@code TIER.at(delta)} with a small delta; ordering that is internal to a
 * single theory lives in that theory's cost holder (e.g. {@code LinearInequationCost} for the
 * integer inequation solver steps), not here. Theory-local constants are deliberately
 * <em>absolute</em> values on the same cost line, not anchored to a band: they order the theory's
 * own steps among each other and are unaffected when a tier is retuned — retuning a band moves
 * exactly those rules that were deliberately placed on it.
 * </p>
 *
 * <p>
 * <b>Care when changing:</b> altering a band's value, or its order relative to other bands,
 * shifts the cross-theory search of <em>all</em> proofs — always re-verify with a full
 * runAllProofs and a Model-Search node-for-node comparison. Respect the hard ordering
 * constraints noted on individual bands (notably {@link #BLOCK_CONTRACT}).
 * </p>
 */
public enum CostBand {
    /**
     * Apply a block/loop contract instead of executing the block. MUST stay more eager (smaller)
     * than {@link #REWRITE} and every symbolic-execution program rule, otherwise the block starts
     * to execute instead of being contracted. Value is the current sentinel; step 3 normalizes it
     * to a modest value between {@link #CLOSE} and {@link #REWRITE}.
     */
    BLOCK_CONTRACT(Long.MIN_VALUE),
    /**
     * Apply a loop invariant instead of unrolling. Only needs to beat loop-unrolling / method
     * expansion when enabled. (Currently above {@link #CLOSE}; step 3 flips it below CLOSE.)
     */
    LOOP_INVARIANT(-20_000),
    /**
     * Close the goal. Most eager of the ordinary bands: eager closure is completeness-neutral
     * (no free-variable calculus), so closing may always take precedence.
     */
    CLOSE(-15_000),
    /** One-Step-Simplification and decidable ground rewrites (rule set {@code concrete}). */
    REWRITE(-11_000),
    /** Force a pending substitution / eager equality ({@code try_apply_subst}). */
    SUBST(-10_000),
    /** Eliminate updates and literals. */
    ELIMINATE(-8_000),
    /** Non-splitting sequent decomposition (alpha rules, update-apply-on-update). */
    DECOMPOSE(-7_000),
    /** Type reasoning (delta rules, type hierarchy). */
    TYPE(-6_000),
    /** Canonicalize / order / commute terms. */
    NORMALIZE(-5_000),
    /** Safe, size-reducing definitional simplification and symbolic-execution steps. */
    SIMPLIFY(-4_500),
    /** Symbolic-execution program step / state merge. */
    EXECUTE(-4_000),
    /** Solve direct (in)equations; apply query axioms. */
    SOLVE(-3_000),
    /** Useful but size-increasing simplification (e.g. comprehension / map unfolding). */
    ENLARGE(-2_000),
    /** Minor local structural preference. */
    PREFER(-500),
    /**
     * The default cost. A taclet whose rule sets carry no explicit feature in a strategy already
     * contributes 0 (the dispatcher sums only the bound rule sets), so binding a rule set to
     * DEFAULT is a deliberate "no strategic bias — apply in due (age) order", cost-identical to
     * leaving it unbound.
     */
    DEFAULT(0),
    /** Defer: lazy definitional unfolding, applied only when needed. */
    DEFER(500),
    /** Strongly defer. */
    DEFER_STRONG(10_000),
    /** Finite last resort — reachable, but only when nothing else applies (soft infinity). */
    LAST_RESORT(1_000_000);

    private final long base;
    private final Feature costFeature;

    CostBand(long base) {
        this.base = base;
        this.costFeature = ConstFeature.createConst(NumberRuleAppCost.create(base));
    }

    /** The band's cost, as a constant strategy {@link Feature} (ready to use in feature terms). */
    public Feature cost() {
        return costFeature;
    }

    /**
     * The band's cost shifted by a small theory-internal ordering delta, as a constant strategy
     * {@link Feature}. Use only for fine ordering within the band; larger, cross-theory steps
     * deserve their own band.
     */
    public Feature at(long delta) {
        return ConstFeature.createConst(NumberRuleAppCost.create(base + delta));
    }

    /** The band's raw cost value. */
    public long value() {
        return base;
    }
}
