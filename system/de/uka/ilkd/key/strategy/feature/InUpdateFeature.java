// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;


public class InUpdateFeature extends BinaryFeature {

    private final boolean inUpdateAndAssume;
    private final boolean splittingRules;
    private final boolean inInitPhase;
    
    private InUpdateFeature(boolean splittingRules, boolean inUpdateAndAssume, 
            boolean inInitPhase) { 
        this.inUpdateAndAssume = inUpdateAndAssume;        
        this.splittingRules = splittingRules;
        this.inInitPhase = inInitPhase;
    }
    
    //true wenn nicht erlaubt
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (app.rule() instanceof Taclet){
            Taclet taclet = (Taclet)app.rule();
            if (taclet.goalTemplates().size()>1 && (!splittingRules || inInitPhase)){
                return true;                
            }
                
            if (taclet.ifSequent().isEmpty()) {
                return false;
            }
        }

        return  !inUpdateAndAssume && inUpdate(pos);
    }
    
 
    public boolean inUpdate(PosInOccurrence pio2){
        if (pio2 == null) {
            return false;
        }
        PosInOccurrence pio = pio2;
        while (!pio.isTopLevel()){
            Operator op = pio.up().subTerm().op();
            if (op instanceof QuanUpdateOperator){
                if (pio.posInTerm().getIndex()<((QuanUpdateOperator)op).targetPos()){
                    return true;
                }

            } else if (op.toString().equals("STATE")) {
        	return true;
            }
            pio = pio.up();
        }        
        return false;
    }
 

    public static Feature create(boolean isSplittingAllowed,
            boolean inUpdateAndAssumes, boolean inInitPhase) {
        return new InUpdateFeature(isSplittingAllowed, inUpdateAndAssumes, inInitPhase);
    }

    
    
    
    
}
