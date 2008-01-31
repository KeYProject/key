package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class WatchPointFeature extends BinaryFeature {

    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        // TODO Auto-generated method stub
        return true;
    }
    public static WatchPointFeature create(){
        return new WatchPointFeature();
    }
}
