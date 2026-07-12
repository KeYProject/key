/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager;
import org.key_project.prover.strategy.costbased.feature.instantiator.CPBranch;
import org.key_project.prover.strategy.costbased.feature.instantiator.ChoicePoint;

import org.jspecify.annotations.NonNull;

public class OneOfCP implements Feature {

    private final Feature[] features;

    private OneOfCP(Feature[] features) {
        this.features = features;
    }

    public static Feature create(Feature[] features) {
        return new OneOfCP(features);
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos,
            Goal goal,
            MutableState mState) {
        final BackTrackingManager manager = mState.getBacktrackingManager();
        // The chosen branch is kept in the per-evaluation MutableState, not in a field of this
        // choice point: one strategy (hence one feature tree, hence this OneOfCP) is shared by all
        // goals, so a field here would be written concurrently by the multi-core prover's workers
        // -- corrupting which branch is read below. A fresh CP is created per evaluation so its
        // choose() writes into this evaluation's MutableState (mirroring ForEachCP).
        manager.passChoicePoint(new CP(mState), this);
        return features[mState.getChoicePointIndex(this)].computeCost(app, pos, goal, mState);
    }

    private final class CP implements ChoicePoint {
        private final MutableState mState;

        private CP(MutableState mState) {
            this.mState = mState;
        }

        private final class BranchIterator implements Iterator<CPBranch> {
            private int num = 0;
            private final RuleApp oldApp;

            public BranchIterator(RuleApp oldApp) {
                this.oldApp = oldApp;
            }

            @Override
            public boolean hasNext() {
                return num < features.length;
            }

            @Override
            public CPBranch next() {
                final int chosen = num++;
                return new CPBranch() {
                    @Override
                    public void choose() {
                        mState.setChoicePointIndex(OneOfCP.this, chosen);
                    }

                    @Override
                    public RuleApp getRuleAppForBranch() {
                        return oldApp;
                    }
                };
            }

            /**
             * throws an unsupported operation exception
             */
            @Override
            public void remove() {
                throw new UnsupportedOperationException();
            }
        }

        @Override
        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            return new BranchIterator(oldApp);
        }
    }
}
