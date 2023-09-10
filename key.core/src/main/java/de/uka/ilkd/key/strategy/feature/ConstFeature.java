/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * A feature that returns a constant value
 */
public class ConstFeature implements Feature {
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return val;
    }

    private ConstFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static Feature createConst(RuleAppCost p_val) {
        return new ConstFeature(p_val);
    }

    public final RuleAppCost getValue() {
        return val;
    }

    private final RuleAppCost val;
}
