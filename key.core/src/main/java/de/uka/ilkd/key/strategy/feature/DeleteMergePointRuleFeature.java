// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.recoderext.MergePointStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Costs for the {@link DeleteMergePointRule}; incredibly cheap if the previous
 * rule application was a {@link MergeRule} app, infinitely expensive otherwise.
 * The alternative would be to always check whether there's another {@link Goal}
 * around with the same {@link MergePointStatement} (then we may not delete),
 * which is much more time intensive.
 *
 * @author Dominic Scheurer
 */
public class DeleteMergePointRuleFeature implements Feature {
    public static final Feature INSTANCE = new DeleteMergePointRuleFeature();

    private DeleteMergePointRuleFeature() {
        // Singleton constructor
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos,
            Goal goal) {
        return goal.node().parent()
                .getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                        ? NumberRuleAppCost.create(-50000)
                        : TopRuleAppCost.INSTANCE;
    }

}
