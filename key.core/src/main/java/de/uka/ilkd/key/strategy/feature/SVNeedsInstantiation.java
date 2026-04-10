/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;

public class SVNeedsInstantiation extends InstantiatedSVFeature {

    public static Feature create(String svName) {
        return new SVNeedsInstantiation(new Name(svName));
    }

    private final Name svName;

    protected SVNeedsInstantiation(Name svName) {
        super(svName);
        this.svName = svName;
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        boolean res = super.filter(app, pos, goal, mState);
        if (!res) {
            for (SchemaVariable sv : app.uninstantiatedVars()) {
                if (sv.name().equals(svName)) {
                    return true;
                }
            }
        }
        return false;
    }


}
