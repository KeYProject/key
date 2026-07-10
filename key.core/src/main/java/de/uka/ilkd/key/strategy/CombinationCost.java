/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * Costs whose meaning spans more than one component strategy — the theory-<em>combination</em>
 * constants, as opposed to the theory-internal holders ({@link FOLCost}, the integer holders,
 * {@link SymExCost}, {@link StringCost}, {@link JavaCardDLCost}, {@link HeapSelectCost}).
 *
 * <p>
 * A constant is admitted here through one of two mechanisms:
 * </p>
 * <ol>
 * <li><b>Conflict-dispatched rule sets</b>: the same rule set is bound by two strategies, and
 * {@link ModularJavaDLStrategy}#resolveConflict dispatches between the two bindings by the focus
 * term (integer-typed focus → Integer half, otherwise FOL half). The two bindings are two halves of
 * ONE combination decision, so their base costs must agree. Currently: {@code apply_equations} and
 * {@code apply_equations_andOr} (the third conflict case, {@code order_terms}, needs no constant
 * here — both halves anchor it at {@code CostBand.NORMALIZE}).</li>
 * <li><b>Cost-sum couplings</b>: one taclet carries rule sets owned by <em>different</em>
 * strategies, so the dispatch sums their contributions and the tuned quantity is the sum, not
 * either summand (e.g. the {@code applyEq} taclet, see {@link #APPLY_SELECT_EQ_EFFECTIVE}).</li>
 * </ol>
 *
 * <p>
 * A theory-local rule may also reference a constant here when sharing the level is the documented
 * intent (e.g. {@code conjNormalForm} at {@link #CNF_CONVERSION}), so that retuning the
 * combination level moves the coupled rule with it.
 * </p>
 *
 * <p>
 * Values are byte-identical to the literals they replace; verify changes with a full runAllProofs
 * (as for {@link org.key_project.prover.strategy.costbased.CostBand}).
 * </p>
 */
final class CombinationCost {
    private CombinationCost() {}

    /**
     * Demodulation: use an oriented equation as a rewrite rule, only in the decreasing direction
     * of the reduction ordering (see the {@code TermSmallerThanFeature} /
     * {@code MonomialsSmallerThanFeature} guards at the call sites; right ≺ left). The FOL half
     * instantiates this with the generic term ordering, the Integer half with the monomial
     * ordering. The orientation step itself ({@code order_terms}) sits at
     * {@code CostBand.NORMALIZE}. Deliberately its own level — <em>not</em> {@code EXECUTE}, which
     * is reserved for symbolic execution.
     */
    static final long ORDERED_REWRITING = -4000;

    /**
     * Priority at which CNF conversion runs: {@code conjNormalForm} (associativity, commutation,
     * distribution, if-then-else expansion — the fine ordering among these comes from the
     * {@code cnf_*} co-rule-sets, {@link FOLCost#CNF_RESTRUCTURE}) and ordered rewriting within
     * and/or clause contexts ({@code apply_equations_andOr}, conflict-dispatched).
     */
    static final long CNF_CONVERSION = -150;

    /**
     * Effective cost of replacing a select term via the {@code applyEq} taclet: the taclet carries
     * BOTH {@code apply_equations} (FOL/Integer, {@link #ORDERED_REWRITING}) and
     * {@code apply_select_eq} (JavaCardDL, {@link HeapSelectCost#APPLY_SELECT_EQ}), so the
     * dispatch sums the two contributions. This constant is the tuned target of that sum;
     * {@link HeapSelectCost#APPLY_SELECT_EQ} is derived from it.
     */
    static final long APPLY_SELECT_EQ_EFFECTIVE = -5700;
}
