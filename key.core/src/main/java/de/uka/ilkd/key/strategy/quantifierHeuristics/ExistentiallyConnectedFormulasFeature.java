/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryTacletAppFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Binary feature that return zero if two given projection term is CS-Releated.
 */
public class ExistentiallyConnectedFormulasFeature extends BinaryTacletAppFeature<Goal> {

    private final ProjectionToTerm for0, for1;

    private ExistentiallyConnectedFormulasFeature(ProjectionToTerm for0,
            ProjectionToTerm for1) {
        this.for0 = for0;
        this.for1 = for1;
    }

    public static Feature create(ProjectionToTerm for0, ProjectionToTerm for1) {
        return new ExistentiallyConnectedFormulasFeature(for0, for1);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        final ClausesGraph graph = ClausesGraph.create(pos.sequentFormula().formula(),
            goal.proof().getServices().getCaches());

        return graph.connected(for0.toTerm(app, pos, goal, mState),
            for1.toTerm(app, pos, goal, mState));
    }

}
