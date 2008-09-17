package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;


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
        return  inUpdate(pos) && !inUpdateAndAssume;
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

    public static Feature create(boolean isSplittingAllowed,
            boolean inUpdateAndAssumes, boolean inInitPhase) {
        return new InUpdateFeature(isSplittingAllowed, inUpdateAndAssumes, inInitPhase);
    }

    
    
    
    
}
