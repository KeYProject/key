// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

import de.uka.ilkd.key.logic.Name;
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
             "EnsuresPost", 
             contract, 
             assumedInvs);
    }
    
    protected Term buildGeneralMemoryAssumption(ProgramVariable selfVar,
            ListOfProgramVariable paramVars) 
        throws ProofInputException {
        Term result = TB.tt();
        Term workingSpace = contract.getWorkingSpace(selfVar, toPV(paramVars), services);
        if(contract.getWorkingSpace(selfVar, toPV(paramVars), services)!=null){
            ProgramVariable initialMemoryArea = services.getJavaInfo().getDefaultMemoryArea();
            Term t_mem = TB.var(initialMemoryArea);
            final ProgramVariable size = services.getJavaInfo().getAttribute(
                    "size", "javax.realtime.MemoryArea");
            final ProgramVariable consumed = services.getJavaInfo().getAttribute(
                    "consumed", "javax.realtime.MemoryArea");
            Function add = (Function) services.getNamespaces().functions().lookup(new Name("add"));
            Function leq = (Function) services.getNamespaces().functions().lookup(new Name("leq")); 
            result = TB.and(result, TB.func(leq, TB.func(add, TB.dot(t_mem,consumed), 
                    workingSpace), TB.dot(t_mem, size)));
        }
        return result;
    }
    
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) throws ProofInputException {        
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
