package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.WatchpointUtil;
import de.uka.ilkd.key.logic.op.Op;

public class WatchPointFeature extends BinaryFeature {

    private final ListOfTerm watchpoints;

    public WatchPointFeature(ListOfTerm watchpoints) {
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

    public static WatchPointFeature create(ListOfTerm wp) {
        return new WatchPointFeature(wp);
    }
}
