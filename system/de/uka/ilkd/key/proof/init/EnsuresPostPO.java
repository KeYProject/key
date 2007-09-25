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
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLTranslationError;


/**
 * The "EnsuresPost" proof obligation. 
 */
public class EnsuresPostPO extends EnsuresPO {
    
    private final OperationContract contract;
    
    public EnsuresPostPO(OperationContract contract,
                         Modality modality,
                         InvariantSelectionStrategy invStrategy) {
        super("EnsuresPost of " + contract.getModelMethod(), 
              contract.getModelMethod(), 
              modality,  
              invStrategy,
              true);
        this.contract = contract;
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map atPreFunctions) throws SLTranslationError {      
        return translatePre(contract, selfVar, toPV(paramVars));
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map atPreFunctions) throws SLTranslationError {        
        Term result = translatePost(contract, 
                                    selfVar, 
                                    toPV(paramVars), 
                                    resultVar, 
                                    exceptionVar);
       
        //add implicit postcondition
        Term implicitPostTerm = tb.tt();
        if(resultVar != null) {
            if(resultVar.sort() instanceof ObjectSort) {       
                implicitPostTerm 
                   = createdFactory.createCreatedOrNullTerm(services, 
                                                            tb.var(resultVar));
            } else {
        	LDT ldt 
        	    = services.getTypeConverter().getModelFor(resultVar.sort());
        	if(ldt instanceof AbstractIntegerLDT) {
        	    Function inBoundsPredicate 
        	    	= ((AbstractIntegerLDT)ldt).getInBoundsPredicate();
        	    if(inBoundsPredicate != null) {
        		implicitPostTerm = tb.func(inBoundsPredicate, 
        					   tb.var(resultVar));
        	    }
        	}
            }
        }
	final Term excNotNullTerm = tb.not(tb.equals(tb.var(exceptionVar), 
	        tb.NULL(services)));
        implicitPostTerm = tb.or(implicitPostTerm, excNotNullTerm);
        result = tb.and(result, implicitPostTerm);

        return result;
    }
}
