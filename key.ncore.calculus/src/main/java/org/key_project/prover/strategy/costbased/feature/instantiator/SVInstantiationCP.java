/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature.instantiator;

import java.util.Iterator;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

/// Feature representing a `ChoicePoint` for instantiating a schema variable of a taclet
/// with the term that is returned by a `ProjectionToTerm`. This feature is useful in
/// particular combined with `ForEachCP`. Although the feature formally is a choice point,
/// it will always have exactly one branch
public class SVInstantiationCP<G extends ProofGoal<G>> implements Feature {
    private final Name svToInstantiate;
    private final ProjectionToTerm<G> value;

    public static <G extends ProofGoal<G>> Feature create(Name svToInstantiate,
            ProjectionToTerm<G> value) {
        return new SVInstantiationCP<G>(svToInstantiate, value);
    }

    public static <G extends ProofGoal<G>> Feature createTriggeredVarCP(ProjectionToTerm<G> value) {
        return new SVInstantiationCP<G>(null, value);
    }


    private SVInstantiationCP(Name svToInstantiate, ProjectionToTerm<G> value) {
        this.svToInstantiate = svToInstantiate;
        this.value = value;
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos,
            Goal goal, MutableState mState) {
        final BackTrackingManager manager = mState.getBacktrackingManager();
        manager.passChoicePoint(new CP(app, pos, (G) goal, mState), this);
        return NumberRuleAppCost.getZeroCost();
    }

    private SchemaVariable findSVWithName(ITacletApp app) {
        if (svToInstantiate == null) {
            return app.taclet().getTrigger().triggerVar();
        }

        final ImmutableSet<SchemaVariable> vars = app.uninstantiatedVars();
        for (SchemaVariable svt : vars) {
            if (svt.name().equals(svToInstantiate)) {
                return svt;
            }
        }

        // Debug.fail("Did not find schema variable " + svToInstantiate
        // + " that I was supposed to instantiate\n" + "(taclet " + app.taclet().name() + ")\n"
        // + "Either the name of the variable is wrong, or the variable\n"
        // + "has already been instantiated.");
        return null;
    }


    private class CP implements ChoicePoint {
        private final PosInOccurrence pos;
        private final RuleApp app;
        private final G goal;
        private final MutableState mState;

        private CP(RuleApp app, PosInOccurrence pos, G goal,
                MutableState mState) {
            this.pos = pos;
            this.app = app;
            this.goal = goal;
            this.mState = mState;
        }

        @Override
        public Iterator<CPBranch> getBranches(RuleApp oldApp) {
            if (!(oldApp instanceof final ITacletApp tapp)) {
                // Debug.fail("Instantiation feature is only applicable to " + "taclet apps, but got
                // ",
                // oldApp);
                throw new IllegalArgumentException(
                    "Rule application must be a taclet application, but is " + oldApp);
            }

            final SchemaVariable sv = findSVWithName(tapp);
            final Term instTerm = value.toTerm(app, pos, goal, mState);

            final RuleApp newApp =
                tapp.addCheckedInstantiation(sv, instTerm,
                    goal.proof().getServices(), true);

            final CPBranch branch = new CPBranch() {
                @Override
                public void choose() {}

                @Override
                public RuleApp getRuleAppForBranch() { return newApp; }
            };

            return ImmutableList.singleton(branch).iterator();
        }

    }
}
