package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public abstract class CompareCostsFeature extends BinaryFeature {

    protected final Feature a, b;
    
    private CompareCostsFeature(Feature a, Feature b) {
        this.a = a;
        this.b = b;
    }

    public static Feature less (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).compareTo (
                       b.compute ( app, pos, goal ) ) < 0;
            }            
        };
    }
    
    public static Feature leq (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).compareTo (
                       b.compute ( app, pos, goal ) ) <= 0;
            }            
        };
    }
    
    public static Feature eq (Feature a, Feature b) {
        return new CompareCostsFeature(a,b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
                return a.compute ( app, pos, goal ).equals (
                       b.compute ( app, pos, goal ) );
            }            
        };
    }
    
}
