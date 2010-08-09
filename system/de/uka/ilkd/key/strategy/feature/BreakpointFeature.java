// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.visualdebugger.BreakpointManager;
import de.uka.ilkd.key.visualdebugger.SourceElementId;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

/**
 * TODO changes this!!!!!!!!!
 * 
 * @author baum
 * 
 */
public class BreakpointFeature extends BinaryFeature {
    BreakpointManager bpManager;
   
    private BreakpointFeature() {
        bpManager = VisualDebugger.getVisualDebugger().getBpManager();
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        try {
            if (app instanceof TacletApp) {
                TacletApp tapp = (TacletApp) app;
                if (bpManager.isNoEx())
                    for (RuleSet next : tapp.taclet().getRuleSets()) {
                        if (next.name().toString().startsWith("method_expand"))
                            return true;
                    }
                
                SourceElementId id = VisualDebugger.getVisualDebugger().getProgramCounter(pos);
                if(id!=null){
/*                    VisualDebugger.print("BP Manger for node "+goal.node().serialNr()+ " "+bpManager+ " StatementId "+id);
                    VisualDebugger.print("Reached StatementID "+id);
                    VisualDebugger.print("Parent StatementIdcount "+goal.node().parent().getNodeInfo().getVisualDebuggerState().getStatementIdcount());*/
                    if (bpManager.suspend(goal.node(),id)){
                        return true;
                    }                   
                }
            }

        } catch (Exception e) {
            e.printStackTrace();
        }
        return false;
    }
    
    public static BreakpointFeature create(){
        return new BreakpointFeature();
    }

}
