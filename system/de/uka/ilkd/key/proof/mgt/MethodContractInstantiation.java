package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.logic.op.Modality;

public class MethodContractInstantiation {
    
    private Expression[] args;    
    private Expression receiver;
    private Expression result;
    private Modality modality;
        
    public MethodContractInstantiation(Expression receiver, 
                                       Expression[] args, 
                                       Expression result,
                                       Modality modality) {
        this.args=args;
        this.receiver=receiver;
        this.result=result;
        this.modality=modality;
    }
    
    public Expression getArgumentAt(int i) {
        return args[i];
    }
    
    public int getArgumentCount() {
        return args.length;
    }
    
    public Expression getResult() {
        return result;
    }
     
    public Expression getReceiver() {
        return receiver;
    }
    
    public Modality getModality() {
        return modality;
    }
}
