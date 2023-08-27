/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class OneOfCP implements Feature {

    private final BackTrackingManager manager;
    private final Feature[] features;

    private int theChosenOne;
    private final ChoicePoint cp = new CP();

    private OneOfCP(BackTrackingManager manager, Feature[] features) {
        this.manager = manager;
        this.features = features;
    }

    public static Feature create(Feature[] features, BackTrackingManager manager) {
        return new OneOfCP(manager, features);
    }

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        manager.passChoicePoint(cp, this);
        return features[theChosenOne].computeCost(app, pos, goal);
    }

    private final class CP implements ChoicePoint {
        private final class BranchIterator implements Iterator<CPBranch> {
            private int num = 0;
            private final RuleApp oldApp;

            public BranchIterator(RuleApp oldApp) {
                this.oldApp = oldApp;
            }

            public boolean hasNext() {
                return num < features.length;
            }

            public CPBranch next() {
                final int chosen = num++;
                return new CPBranch() {
                    public void choose() {
                        theChosenOne = chosen;
                    }

                    public RuleApp getRuleAppForBranch() {
                        return oldApp;
                    }
                };
            }

            /**
             * throws an unsupported operation exception
             */
            public void remove() {
                throw new UnsupportedOperationException();
            }
        }

        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            return new BranchIterator(oldApp);
        }
    }
}
