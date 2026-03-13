/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termProjection;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.Nullable;

/// Interface for mappings from rule applications to terms. This is used, for instance, for
/// determining the instantiation of a schema variable. We also allow projections to be partial,
/// which is signalled by <code>toTerm</code> returning <code>null</code>
public interface ProjectionToTerm<Goal extends ProofGoal<Goal>> {
    @Nullable
    Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState);
}
