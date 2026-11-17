/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/// A feature that computes the sum of the values of a feature term when a given variable ranges
/// over
/// a sequence of terms
// @StableCost: transparent -- it sums its (recursed) body over a TermGenerator. CostReuse also
// classifies that generator: it stays local only with a find-local generator (e.g.
// SuperTermGenerator), and is non-local with a sequent-scanning one (SequentFormulasGenerator).
@StableCost
public class ComprehendedSumFeature implements Feature {
    private final TermBuffer var;
    private final TermGenerator generator;
    private final Feature body;

    /// @param var`TermBuffer` in which the terms are going to be stored
    /// @param generator the terms that are to be iterated over
    /// @param body a feature that is supposed to be evaluated repeatedly for the possible values of
    /// `var`
    public static Feature create(TermBuffer var, TermGenerator generator, Feature body) {
        return new ComprehendedSumFeature(var, generator, body);
    }

    private ComprehendedSumFeature(TermBuffer var, TermGenerator generator,
            Feature body) {
        this.var = var;
        this.generator = generator;
        this.body = body;
    }

    @Override
    public RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, ProofGoal<?> goal, MutableState mState) {
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
