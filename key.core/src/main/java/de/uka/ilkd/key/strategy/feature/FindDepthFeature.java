/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * A feature that computes the depth of the find-position of a taclet (top-level positions have
 * depth zero or if not a find taclet)
 *
 * TODO: eliminate this class and use term features instead
 */
public class FindDepthFeature implements Feature {

    public static final Feature INSTANCE = new FindDepthFeature();

    private FindDepthFeature() {}

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        // assert pos != null : "Feature is only applicable to rules with find";

        return NumberRuleAppCost.create(pos == null ? 0 : pos.depth());
    }

}
