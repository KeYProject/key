/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/// FOL-theory-internal ordering costs, used by [org.key_project.prover.strategy.FOLStrategy]. These
/// are the fine, within-FOL
/// ordering values that are _reused_ across FOLStrategy's normalization / splitting /
/// equation methods and therefore deserve a name of their own; genuinely one-off nudges are written
/// directly as `CostBand.<band>.at(delta)` at the call site instead.
///
/// Values are byte-identical to the literals they replace. They position FOL rules within the
/// shared
/// [CostBand] ladder, so changing one shifts the
/// cross-theory search — verify with a full runAllProofs and a Model-Search node-for-node
/// comparison
/// (as for [CostBand]).
///
final public class FOLCost {
    private FOLCost() {}

    /// Distribution / swapping of quantifiers (`distrQuantifier`, `swapQuantifiers`).
    static public final long QUANTIFIER_DISTRIBUTION = -300;

    /// Restructuring of CNF clauses by associativity / distribution (`cnf_orAssoc`,
    /// `cnf_andAssoc`, `cnf_dist`); the small `± delta` at the call sites orders
    /// these among themselves. These are the fine deltas summed on top of the
    /// [CombinationCost#CNF_CONVERSION] level via the dual rule-set tags of the
    /// `conjNormalForm` taclets.
    static public final long CNF_RESTRUCTURE = -35;

    /// Defer `replace_known_right` when its target is in the consequent of an implication or
    /// inside an equivalence, so the connective is decomposed first (which makes the antecedent
    /// available as a known-true fact). Deliberately _not_ applied to
    /// `replace_known_left`, whose antecedent-true facts stay valid across the decomposition.
    static public final long REPLACE_KNOWN_UNDER_CONNECTIVE = 100;

    /// Standard cost of a direct cut (`cut_direct`).
    static public final long CUT_DIRECT_STANDARD = 100;

    /// Preferred direction of the `pullOutQuantifier*` rules.
    static public final long PULL_OUT_QUANTIFIER = -20;

    /// Dispreferred direction of the `pullOutQuantifier*` rules.
    static public final long PULL_OUT_QUANTIFIER_REVERSE = -40;
}
