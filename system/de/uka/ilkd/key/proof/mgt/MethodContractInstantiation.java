// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
