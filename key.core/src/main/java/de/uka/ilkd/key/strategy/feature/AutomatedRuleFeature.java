/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.rulefilter.AnyRuleSetTacletFilter;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * This feature checks if a rule may be applied automatically. Currently this does not apply to
 * rules which are not member of any rule set.
 */
public class AutomatedRuleFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new AutomatedRuleFeature();

    private AutomatedRuleFeature() {}

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return AnyRuleSetTacletFilter.INSTANCE.filter(app.rule());
    }

}
