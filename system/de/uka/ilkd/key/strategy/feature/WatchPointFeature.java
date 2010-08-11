// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchpointUtil;

public class WatchPointFeature extends BinaryFeature {

    private final List<WatchPoint> watchpoints;

    public WatchPointFeature(List<WatchPoint> watchpoints) {
        super();
        this.watchpoints = watchpoints;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {

        assert watchpoints != null : "Watchpoints are NULL!";
        if (watchpoints.isEmpty()) {
            return false;
        } else {

            return WatchpointUtil.evalutateWatchpoints(goal.node(), watchpoints, goal
                    .sequent(), pos, goal.proof(), Op.OR, false, 250);
        }
    }

    public static WatchPointFeature create(List<WatchPoint> wp) {
        return new WatchPointFeature(wp);
    }
}
