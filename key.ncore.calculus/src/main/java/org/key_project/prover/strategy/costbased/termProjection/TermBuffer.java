/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.termProjection;


import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Projection that can store and returns an arbitrary term or formula. Objects of this class are
/// mainly used like bound variables and together with features like <code>LetFeature</code> and
/// <code>ForEachCP</code>.
public class TermBuffer<Goal extends ProofGoal<Goal>> implements ProjectionToTerm<Goal> {

    public Term getContent(MutableState mState) {
        return mState.read(this);
    }

    public void setContent(Term t, MutableState mState) {
        mState.assign(this, t);
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return getContent(mState);
    }
}
