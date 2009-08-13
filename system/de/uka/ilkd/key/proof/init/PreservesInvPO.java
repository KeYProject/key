// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
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
        super(initConfig, name, programMethod, Modality.BOX, assumedInvs, false);
        this.ensuredInvs = ensuredInvs;
    }
    
    
    public PreservesInvPO(InitConfig initConfig,
	    		  ProgramMethod programMethod, 
                          SetOfClassInvariant assumedInvs,
                          SetOfClassInvariant ensuredInvs) {
        this(initConfig, 
             "PreservesInv (" + programMethod + ")", 
             programMethod, 
             assumedInvs, 
             ensuredInvs);
    }
    
    
    @Override
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Term heapAtPre) throws ProofInputException {
        return TB.tt();
    }
    
    
    @Override
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Term heapAtPre) throws ProofInputException {        
        return translateInvs(ensuredInvs);
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof PreservesInvPO)) {
            return false;
        }
        PreservesInvPO piPO = (PreservesInvPO) po;
        return programMethod.equals(piPO.programMethod)
        	&& modality.equals(piPO.modality)
        	&& piPO.ensuredInvs.subset(ensuredInvs) 
                && assumedInvs.subset(piPO.assumedInvs);
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof PreservesInvPO)) {
            return false;
        }
        PreservesInvPO po = (PreservesInvPO) o;
        return super.equals(po)
               && ensuredInvs.equals(po.ensuredInvs);
    }
    
    
    @Override
    public int hashCode() {
        return super.hashCode() + ensuredInvs.hashCode();
    }
}
