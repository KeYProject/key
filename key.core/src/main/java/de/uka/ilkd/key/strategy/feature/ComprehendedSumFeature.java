/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/**
 * A feature that computes the sum of the values of a feature term when a given variable ranges over
 * a sequence of terms
 */
public class ComprehendedSumFeature implements Feature<Goal> {

    private final TermBuffer<Goal> var;
    private final TermGenerator<Goal> generator;
    private final Feature<Goal> body;

    /**
     * @param var <code>TermBuffer</code> in which the terms are going to be stored
     * @param generator the terms that are to be iterated over
     * @param body a feature that is supposed to be evaluated repeatedly for the possible values of
     *        <code>var</code>
     */
    public static Feature<Goal> create(TermBuffer<Goal> var, TermGenerator<Goal> generator,
            Feature<Goal> body) {
        return new ComprehendedSumFeature(var, generator, body);
    }

    private ComprehendedSumFeature(TermBuffer<Goal> var, TermGenerator<Goal> generator,
            Feature<Goal> body) {
        this.var = var;
        this.generator = generator;
        this.body = body;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        final Term outerVarContent = var.getContent(mState);

        final var it = generator.generate(app, pos, goal, mState);
        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        while (it.hasNext() && !(res instanceof TopRuleAppCost)) {
            var.setContent(it.next(), mState);

            res = res.add(body.computeCost(app, pos, goal, mState));
        }

        var.setContent(outerVarContent, mState);
        return res;
    }
}
