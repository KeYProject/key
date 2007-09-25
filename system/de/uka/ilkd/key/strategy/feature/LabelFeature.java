package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.visualdebugger.PCLabel;



public class LabelFeature extends BinaryFeature {
    
    private LabelFeature(){        
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (goal.node().root())
            return false;

        if (goal.node().parent().getAppliedRuleApp().posInOccurrence()==null)
            return false;

        PosInOccurrence pio = goal.node().parent().getAppliedRuleApp().posInOccurrence().topLevel();
        if( goal.node().parent().getNodeInfo().getVisualDebuggerState().getLabels().containsKey(pio)){
            if (((PCLabel)goal.node().parent().getNodeInfo().getVisualDebuggerState().getLabels().get(pio)).isLooking())
                return true;
            if( goal.node().parent().getNodeInfo().getActiveStatement()!=null)
                return true; //TODO act statement in prog mod

        }

        return false;
    }
    
    public static LabelFeature create(){
        return new LabelFeature();
    }

}


