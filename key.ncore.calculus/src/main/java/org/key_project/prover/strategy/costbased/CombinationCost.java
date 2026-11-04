/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/**
 * Costs whose meaning spans more than one component strategy — the theory-<em>combination</em>
 * constants, as opposed to the theory-internal holders (like {@link FOLCost} and the integer
 * holders).
 *
 * <p>
 * A theory-local rule may also reference a constant here when sharing the level is the documented
 * intent (e.g. {@code conjNormalForm} at {@link #CNF_CONVERSION}), so that retuning the
 * combination level moves the coupled rule with it.
 * </p>
 *
 * <p>
 * Values are byte-identical to the literals they replace; verify changes with a full runAllProofs
 * (as for {@link CostBand}).
 * </p>
 */
final public class CombinationCost {
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
    static public final long ORDERED_REWRITING = -4000;

    /**
     * Priority at which CNF conversion runs: {@code conjNormalForm} (associativity, commutation,
     * distribution, if-then-else expansion — the fine ordering among these comes from the
     * {@code cnf_*} co-rule-sets, {@link FOLCost#CNF_RESTRUCTURE}) and ordered rewriting within
     * and/or clause contexts ({@code apply_equations_andOr}, conflict-dispatched).
     */
    static public final long CNF_CONVERSION = -150;
}
