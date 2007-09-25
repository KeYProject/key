package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.visualdebugger.BreakpointManager;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;


public class InUpdateFeature extends BinaryFeature {


    public static boolean inUpdateAndAssume = false;
    
    BreakpointManager bpManager;
    ListOfNamed h;
    public static boolean splitting_rules=true;
    
    private InUpdateFeature(Proof p){        
 
    }
    
    //true wenn nicht erlaubt
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if (app.rule() instanceof Taclet){
            Taclet taclet = (Taclet)app.rule();
            if (taclet.goalTemplates().size()>1 && !splitting_rules){
                return true;                
            }
    
            if (taclet.goalTemplates().size()>1 && VisualDebugger.getVisualDebugger().isInitPhase()){
                return true;                
            }
            
            if (taclet.ifSequent()==Sequent.EMPTY_SEQUENT)//&&
                    //(((Taclet)app.rule()).goalTemplates().size()==1||inState(pos))){
                return false;
           // }
        }
        return  inUpdate(pos) && !inUpdateAndAssume;
    }
    
    public static InUpdateFeature create(Proof p){
        return new InUpdateFeature(p);
    }
    
    
    public boolean inUpdate(PosInOccurrence pio2){
        if (pio2 == null) {
            return false;
        }
        PosInOccurrence pio = pio2;
        while (!pio.isTopLevel()){
            Operator op = pio.up().subTerm().op();
            if (op instanceof QuanUpdateOperator|| op.toString().equals("STATE")){
                if (pio.posInTerm().getIndex()< pio.up().subTerm().arity()-1){
                    return true;
                }

            }            
            pio = pio.up();
        }        
        return false;
    }
 
    public boolean inState(PosInOccurrence pio2){
        PosInOccurrence pio = pio2;
        if (pio2==null){
         return false;
        }
        while (!pio.isTopLevel()){
            Operator op = pio.up().subTerm().op();
            if (op.toString().equals("STATE")){
                return true;                             
            }            
            pio = pio.up();
        }
        
        return false;
    }

    
    
    
    
}
