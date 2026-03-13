/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

///
/// There can be several candidates for matching a formula of an assumes clause of a taclet. This
/// record keeps for a given formula the list of successful instantiations for the sequent formula
/// as well as their corresponding math results (match conditions) that break down the candidate
/// formula to instantiations of the schema variables that made up the assumes-formula.
///
/// It is not sufficient to simply keep the match conditions as for the taclet application itself
/// the candidate information is used to decide whether to split the goal or not.
/// See [AssumesFormulaInstantiation] and subclasses for more details.
///
/// The two lists are paired in the sense that the match conditions for the i-th candidate can be
/// found at the i-th position of list `matchConditions`.
///
/// @param candidates the list of candidate instantiations
/// @param matchConditions the list of match conditions
public record AssumesMatchResult(ImmutableList<@NonNull AssumesFormulaInstantiation> candidates,
        ImmutableList<@NonNull MatchResultInfo> matchConditions) {
}
