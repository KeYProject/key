/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * A feature that computes the sum of the values of a feature term when a given variable ranges over
 * a sequence of terms
 */
public class ComprehendedSumFeature implements Feature {

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
        return new ComprehendedSumFeature(var, generator, body);
    }

    private ComprehendedSumFeature(TermBuffer var, TermGenerator generator, Feature body) {
        this.var = var;
        this.generator = generator;
        this.body = body;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        final Term outerVarContent = var.getContent(mState);

        final Iterator<Term> it = generator.generate(app, pos, goal, mState);
        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        while (it.hasNext() && !(res instanceof TopRuleAppCost)) {
            var.setContent(it.next(), mState);

            res = res.add(body.computeCost(app, pos, goal, mState));
        }

        var.setContent(outerVarContent, mState);
        return res;
    }
}
