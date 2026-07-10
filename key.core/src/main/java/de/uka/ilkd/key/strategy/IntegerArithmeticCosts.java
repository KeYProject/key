/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/*
 * Theory-internal cost constants for the integer arithmetic strategy, grouped by the arithmetic
 * sub-theory they belong to. The grouping deliberately anticipates a future split of
 * IntegerStrategy into separate sub-strategies (polynomial / linear / non-linear / div-mod): each
 * holder is meant to move with its sub-strategy. Cross-theory levels stay in
 * {@link org.key_project.prover.strategy.costbased.CostBand}; only the arithmetic-internal ordering
 * lives here. All values are byte-identical to the literals they replace.
 */

/** Polynomial normal-form canonicalisation (Buchberger normalisation) — the "basic" substrate. */
final class PolynomialCost {
    private PolynomialCost() {}

    /** elimSubNeg, homo, pullOutFactor, elimOneLeft/Right. */
    static final long EXPAND = -120;
    static final long MUL_ORDER = -100;
    static final long MUL_ASSOC = -80;
    static final long ADD_ORDER = -60;
    static final long ADD_ASSOC = -10;
    /** polySimp_dist base; the distLeft sub-case is {@code DISTRIBUTE + 20}. */
    static final long DISTRIBUTE = -35;
    static final long PULLOUT_GCD = -2250;
}


/**
 * Polynomial <em>equation solving</em> (Gaussian / Gröbner). These {@code polySimp_*} rule sets
 * live
 * here rather than in {@link PolynomialCost} on purpose: they do not just canonicalise a term, they
 * <em>derive</em> from and apply equations, so they belong to the "linear" (solving) layer next to
 * {@link LinearInequationCost}.
 */
final class LinearEquationCost {
    private LinearEquationCost() {}

    // The base costs of apply_equations / apply_equations_andOr are combination-shared with
    // FOLStrategy (conflict-dispatched; the Integer halves use the monomial ordering as
    // demodulation guard): see CombinationCost.ORDERED_REWRITING and
    // CombinationCost.CNF_CONVERSION.

    /** polySimp_balance, polySimp_normalise. */
    static final long BALANCE = -30;
    /**
     * polySimp_applyEq — the monomial-coefficient-specialised equation application (the general
     * demodulation cost is {@link CombinationCost#ORDERED_REWRITING}). The rigid variant
     * polySimp_applyEqRigid is written {@code APPLY_EQ + 1} at the call site; that +1 is only an
     * (uninteresting) tie-break between the two rules, a step-3 candidate to flatten to a single
     * cost. Step-3 idea: test whether this specialised variant is needed at all, or should just be
     * a small delta preferring the original {@code apply_equations} rules.
     */
    static final long APPLY_EQ = 1;
}


/** Linear inequation solving — the Omega / Fourier-Motzkin machinery ({@code inEqSimp_*}). */
final class LinearInequationCost {
    private LinearInequationCost() {}

    static final long PROPAGATION = -2400;
    static final long SATURATE = -1900;
    /** General GCD normalisation of inequations — confluent, hence safe to apply eagerly. */
    static final long PULLOUT_GCD_CONFLUENT = -2150;
    static final long FOR_NORMALISATION = -1100;
    static final long MOVE_LEFT = -90;
    static final long MAKE_NON_STRICT = -80;
    static final long CONTRAD = -60;
    static final long COMMUTE = -40;
    static final long STRENGTHEN = -30;
    static final long ANTISYMM = -20;
    /**
     * Faster antecedent-specialised GCD pull-out, but <em>not</em> confluent (the result can depend
     * on application order), hence pinned near baseline so it fires only opportunistically — in
     * contrast to the eager {@link #PULLOUT_GCD_CONFLUENT}.
     */
    static final long PULLOUT_GCD_ANTEC_NONCONFLUENT = -10;
}


/** Non-linear arithmetic — cross-multiplication, sign cases, root inferences (Model Search). */
final class NonlinearArithmeticCost {
    private NonlinearArithmeticCost() {}

    /**
     * inEqSimp_nonLin (cross-multiplication) base; case-distinction offsets are
     * {@code MULTIPLY + n}.
     */
    static final long MULTIPLY = 1000;
    /**
     * Divide an inequation by a factor of known sign/bound to bound the quotient (the
     * {@code divide_inEq*} taclets) — the inverse of cross-multiplication. Kept clearly more eager
     * than {@link #MULTIPLY}, since dividing/reducing is safer and more productive than
     * multiplying.
     */
    static final long DIVIDE_INEQUATION = -1400;
    static final long SPLIT_EQ = -100;
}


/** Division / modulo and DefOps expansion ({@code polyDivision}, {@code defOps_*}). */
final class DivModCost {
    private DivModCost() {}

    static final long POLY_DIVISION = -2250;
    static final long EXPAND_MODULO = -600;
    /** extra cost for defOps_div/jdiv applied below a modality. */
    static final long BELOW_MODALITY = 200;
    static final long EXPAND_RANGES = -8000;
    static final long MOD_HOMO_EQ = -5000;
    static final long EXPAND_NUMERIC_OP = -500;
    /** defOps_jdiv_inline for a literal numerator (eager, concrete division). */
    static final long INLINE = -5000;
    /** literal-only division / modulo (defOps_mod, off-mode jdiv_inline). */
    static final long MOD = -4000;
    /** modulo expansion for a polynomial (non-literal) modulus (defOps_mod). */
    static final long MOD_EXPAND = -3500;
}
