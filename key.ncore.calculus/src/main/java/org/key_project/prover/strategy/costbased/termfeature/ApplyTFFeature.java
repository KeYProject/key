/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.termfeature;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/// Feature for invoking a term feature on the instantiation of a schema variable
@StableCost
public class ApplyTFFeature implements Feature {
    private final ProjectionToTerm proj;
    private final TermFeature termFeature;
    private final RuleAppCost noInstCost;
    private final boolean demandInst;

    /// @param proj the ProjectionToTerm to the instantiation is supposed to be inspected
    /// @param termFeature the term feature to use
    /// @param noInstCost result if <code>schemaVar</code> is not instantiated
    /// @param demandInst if <code>true</code> then raise an exception if <code>schemaVar</code> is
    /// not instantiated (otherwise: return <code>noInstCost</code>)
    private ApplyTFFeature(ProjectionToTerm proj, TermFeature termFeature,
            RuleAppCost noInstCost,
            boolean demandInst) {
        this.proj = proj;
        this.termFeature = termFeature;
        this.noInstCost = noInstCost;
        this.demandInst = demandInst;
    }

    public static Feature createNonStrict(ProjectionToTerm proj, TermFeature tf,
            RuleAppCost noInstCost) {
        return new ApplyTFFeature(proj, tf, noInstCost, false);
    }

    public static Feature create(ProjectionToTerm proj, TermFeature tf) {
        return new ApplyTFFeature(proj, tf, TopRuleAppCost.INSTANCE, true);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState) {
        final Term te = proj.toTerm(app, pos, goal, mState);
        if (te == null) {
            assert !demandInst : "ApplyTFFeature: got undefined argument (null)";
            return noInstCost;
        }

        return termFeature.compute(te, mState, goal.proof().getServices());
    }
}
