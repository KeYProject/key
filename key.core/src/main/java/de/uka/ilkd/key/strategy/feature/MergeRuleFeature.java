/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.merge.MergeRule;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

/**
 * Costs for the {@link MergeRule}; cheap if the first statement in the chosen top-level formula is
 * a {@link MergePointStatement}, otherwise, infinitely expensive.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleFeature implements Feature {
    public static final Feature INSTANCE = new MergeRuleFeature();

    private MergeRuleFeature() {
        // Singleton constructor
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal,
            MutableState mState) {
        final JTerm t = (JTerm) pos.subTerm();
        if (!pos.isTopLevel() || !t.containsJavaBlockRecursive()) {
            return TopRuleAppCost.INSTANCE;
        }

        return JavaTools.getActiveStatement(
            TermBuilder.goBelowUpdates(t).javaBlock()) instanceof MergePointStatement
                    ? NumberRuleAppCost.create(0)
                    : TopRuleAppCost.INSTANCE;
    }

}
