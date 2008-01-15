// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


/**
 * The "PreservesThroughout" proof obligation. 
 */
public class PreservesThroughoutPO extends EnsuresPO {
    
    private SetOfClassInvariant invs;
    
    public PreservesThroughoutPO(InitConfig initConfig,
	    			 ProgramMethod programMethod, 
                                 SetOfClassInvariant invs) {
        super(initConfig,
              "PreservesThroughout", 
              programMethod, 
              Op.TOUT,
              invs,
              true);
        this.invs = invs;
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map atPreFunctions) throws ProofInputException {
        return TB.tt();
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map atPreFunctions) throws ProofInputException {        
        return translateInvs(invs);
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof PreservesThroughoutPO)) {
            return false;
        }
        PreservesThroughoutPO po = (PreservesThroughoutPO) o;
        return super.equals(po)
               && invs.equals(po.invs);
    }
    
    
    public int hashCode() {
        return super.hashCode() + invs.hashCode();
    }
}
