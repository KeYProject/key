/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.AnyRuleSetTacletFilter;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * This feature checks if a rule may be applied automatically. Currently this does not apply to
 * rules which are not member of any rule set.
 */
public class AutomatedRuleFeature extends BinaryTacletAppFeature {

    public static final Feature<Goal> INSTANCE = new AutomatedRuleFeature();

    private AutomatedRuleFeature() {}

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return AnyRuleSetTacletFilter.INSTANCE.filter(app.rule());
    }

}
