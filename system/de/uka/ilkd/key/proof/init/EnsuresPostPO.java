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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


/**
 * The "EnsuresPost" proof obligation. 
 */
public class EnsuresPostPO extends EnsuresPO {
    
    private final OperationContract contract;
    
    public EnsuresPostPO(InitConfig initConfig, 
                         String name,
                         OperationContract contract, 
                         SetOfClassInvariant assumedInvs) {
        super(initConfig, 
              name, 
              contract.getProgramMethod(), 
              contract.getModality(), 
              assumedInvs, 
              true);
        this.contract = contract;
    }


    public EnsuresPostPO(InitConfig initConfig, OperationContract contract,
            SetOfClassInvariant assumedInvs) {
        this(initConfig, 
             "EnsuresPost (" 
                 + contract.getProgramMethod() + ", " 
                 + contract.getDisplayName() + ")", 
             contract, 
             assumedInvs);
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) 
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) 
            throws ProofInputException {        
        Term result = translatePost(contract, 
                                    selfVar, 
                                    toPV(paramVars), 
                                    resultVar, 
                                    exceptionVar,
                                    atPreFunctions);
       
        //add implicit postcondition (see discussion for Bug #789) 
        /*
        Term implicitPostTerm = TB.tt();
        if(resultVar != null) {
            if(resultVar.sort() instanceof ObjectSort) {       
                implicitPostTerm 
                   = createdFactory.createCreatedOrNullTerm(services, 
                                                            TB.var(resultVar));
            } else {
        	LDT ldt 
        	    = services.getTypeConverter().getModelFor(resultVar.sort());
        	if(ldt instanceof AbstractIntegerLDT) {
        	    Function inBoundsPredicate 
        	    	= ((AbstractIntegerLDT)ldt).getInBoundsPredicate();
        	    if(inBoundsPredicate != null) {
        		implicitPostTerm = TB.func(inBoundsPredicate, 
        					   TB.var(resultVar));
        	    }
        	}
            }
        }
	Term excNotNullTerm = TB.not(TB.equals(TB.var(exceptionVar), 
			                       TB.NULL(services)));
        implicitPostTerm = TB.or(implicitPostTerm, excNotNullTerm);
        result = TB.and(result, implicitPostTerm);
        */

        return result;
    }
    
    
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO epPO = (EnsuresPostPO) po;
        return specRepos.splitContract(epPO.contract)
                        .subset(specRepos.splitContract(contract))
               && assumedInvs.subset(epPO.assumedInvs);
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO po = (EnsuresPostPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }
    
    
    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
