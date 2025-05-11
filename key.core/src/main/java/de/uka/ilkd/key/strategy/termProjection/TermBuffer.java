/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.MutableState;
import org.jspecify.annotations.NonNull;

/**
 * Projection that can store and returns an arbitrary term or formula. Objects of this class are
 * mainly used like bound variables and together with features like <code>LetFeature</code> and
 * <code>ForEachCP</code>.
 */
public class TermBuffer implements ProjectionToTerm {



    public Term getContent(@NonNull MutableState mState) {
        return mState.read(this);
    }

    public void setContent(Term t, @NonNull MutableState mState) {
        mState.assign(this, t);
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, @NonNull MutableState mState) {
        return getContent(mState);
    }

}
