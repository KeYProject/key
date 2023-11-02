/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.instantiator;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.MutableState;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;


/**
 * Feature representing a <code>ChoicePoint</code> that iterates over the terms returned by a
 * <code>TermGenerator</code>. The terms are stored in a <code>TermBuffer</code> one after the other
 * and can subsequently be used to instantiate a rule application
 */
public class ForEachCP implements Feature {

    private final TermBuffer var;
    private final TermGenerator generator;
    private final Feature body;

    /**
     * @param var <code>TermBuffer</code> in which the terms are going to be stored
     * @param generator the terms that are to be iterated over
     * @param body a feature that is supposed to be evaluated repeatedly for the possible values of
     *        <code>var</code>
     */
    public static Feature create(TermBuffer var, TermGenerator generator, Feature body) {
        return new ForEachCP(var, generator, body);
    }

    private ForEachCP(TermBuffer var, TermGenerator generator, Feature body) {
        this.var = var;
        this.generator = generator;
        this.body = body;
    }

    public RuleAppCost computeCost(final RuleApp app, final PosInOccurrence pos, final Goal goal, MutableState mState) {
        final Term outerVarContent = var.getContent(mState);
        var.setContent(null, mState);

        final BackTrackingManager manager = mState.getBacktrackingManager();
        manager.passChoicePoint(new CP(app, pos, goal, mState), this);

        final RuleAppCost res;
        if (var.getContent(mState) != null) {
            res = body.computeCost(app, pos, goal, mState);
        } else {
            res = NumberRuleAppCost.getZeroCost();
        }

        var.setContent(outerVarContent, mState);
        return res;
    }

    private final class CP implements ChoicePoint {
        private final class BranchIterator implements Iterator<CPBranch> {
            private final Iterator<Term> terms;
            private final RuleApp oldApp;

            private final MutableState mState;

            private BranchIterator(Iterator<Term> terms, RuleApp oldApp, MutableState mState) {
                this.terms = terms;
                this.oldApp = oldApp;
                this.mState = mState;
            }

            public boolean hasNext() {
                return terms.hasNext();
            }

            public CPBranch next() {
                final Term generatedTerm = terms.next();
                return new CPBranch() {
                    public void choose() {
                        var.setContent(generatedTerm, mState);
                    }

                    public RuleApp getRuleAppForBranch() {
                        return oldApp;
                    }
                };
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }
        }

        private final PosInOccurrence pos;
        private final RuleApp app;
        private final Goal goal;
        private final MutableState mState;

        private CP(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
            this.pos = pos;
            this.app = app;
            this.goal = goal;
            this.mState = mState;
        }

        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            return new BranchIterator(generator.generate(app, pos, goal, mState), oldApp, mState);
        }
    }

}
