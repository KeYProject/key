package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.visualdebugger.HashMapFromPosInOccurrenceToLabel;
import de.uka.ilkd.key.visualdebugger.PCLabel;



public class LabelFeature extends BinaryFeature {
    
    public static final LabelFeature INSTANCE = new LabelFeature();
    
    private LabelFeature(){        
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (goal.node().root())
            return false;

        final Node parent = goal.node().parent();
        final RuleApp previouslyAppliedRuleApp = parent.getAppliedRuleApp();
        if (previouslyAppliedRuleApp.posInOccurrence()==null)
            return false;

        final PosInOccurrence pio = previouslyAppliedRuleApp.posInOccurrence().topLevel();
        
        final NodeInfo nodeInfo = parent.getNodeInfo();
        final HashMapFromPosInOccurrenceToLabel debugLabels = 
            nodeInfo.getVisualDebuggerState().getLabels();
        
        if( debugLabels.containsKey(pio)){
            if (((PCLabel)debugLabels.get(pio)).isLooking()) {
                return true;
            }
            if( nodeInfo.getActiveStatement() != null) {
                return true; //TODO act statement in prog mod
            }
        }

        return false;
    }
}


