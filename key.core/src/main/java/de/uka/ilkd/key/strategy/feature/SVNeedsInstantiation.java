/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

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
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        boolean res = super.filter(app, pos, goal);
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
