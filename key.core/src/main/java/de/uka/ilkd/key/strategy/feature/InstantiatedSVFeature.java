/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termProjection.SVInstantiationProjection;

/**
 * Feature that returns zero iff a certain schema variable is instantiated. If the schemavariable is
 * not instantiated schema variable or does not occur in the taclet infinity costs are returned.
 */
public class InstantiatedSVFeature extends BinaryTacletAppFeature {

    private final ProjectionToTerm instProj;

    public static Feature create(Name svName) {
        return new InstantiatedSVFeature(svName);
    }

    protected InstantiatedSVFeature(Name svName) {
        instProj = SVInstantiationProjection.create(svName, false);
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return instProj.toTerm(app, pos, goal) != null;
    }

}
