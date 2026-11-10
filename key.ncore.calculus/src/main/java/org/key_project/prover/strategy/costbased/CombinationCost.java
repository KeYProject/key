/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/// Costs whose meaning spans more than one component strategy — the theory-_combination_
/// constants, as opposed to the theory-internal holders (like [FOLCost] and the integer
/// holders).
///
/// A theory-local rule may also reference a constant here when sharing the level is the documented
/// intent (e.g. `conjNormalForm` at [#CNF_CONVERSION]), so that retuning the
/// combination level moves the coupled rule with it.
///
/// Values are byte-identical to the literals they replace; verify changes with a full runAllProofs
/// (as for [CostBand]).
///
final public class CombinationCost {
    private CombinationCost() {}

    /// Demodulation: use an oriented equation as a rewrite rule, only in the decreasing direction
    /// of the reduction ordering (see the `TermSmallerThanFeature` /
    /// `MonomialsSmallerThanFeature` guards at the call sites; right ≺ left). The FOL half
    /// instantiates this with the generic term ordering, the Integer half with the monomial
    /// ordering. The orientation step itself (`order_terms`) sits at
    /// `CostBand.NORMALIZE`. Deliberately its own level — _not_`EXECUTE`, which
    /// is reserved for symbolic execution.
    static public final long ORDERED_REWRITING = -4000;

    /// Priority at which CNF conversion runs: `conjNormalForm` (associativity, commutation,
    /// distribution, if-then-else expansion — the fine ordering among these comes from the
    /// `cnf_*` co-rule-sets, [FOLCost#CNF_RESTRUCTURE]) and ordered rewriting within
    /// and/or clause contexts (`apply_equations_andOr`, conflict-dispatched).
    static public final long CNF_CONVERSION = -150;
}
