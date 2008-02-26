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
 * The "PreservesInv" proof obligation. 
 */
public class PreservesInvPO extends EnsuresPO {
    
    private final SetOfClassInvariant ensuredInvs;
    
    
    protected PreservesInvPO(InitConfig initConfig,
	    		     String name,
                             ProgramMethod programMethod,
                             SetOfClassInvariant assumedInvs,
                             SetOfClassInvariant ensuredInvs) {
        super(initConfig, name, programMethod, Op.BOX, assumedInvs, false);
        this.ensuredInvs = ensuredInvs;
    }
    
    
    public PreservesInvPO(InitConfig initConfig,
	    		  ProgramMethod programMethod, 
                          SetOfClassInvariant assumedInvs,
                          SetOfClassInvariant ensuredInvs) {
        this(initConfig, 
             "PreservesInv", 
             programMethod, 
             assumedInvs, 
             ensuredInvs);
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
        return translateInvs(ensuredInvs);
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof PreservesInvPO)) {
            return false;
        }
        PreservesInvPO po = (PreservesInvPO) o;
        return super.equals(po)
               && ensuredInvs.equals(po.ensuredInvs);
    }
    
    
    public int hashCode() {
        return super.hashCode() + ensuredInvs.hashCode();
    }
}
