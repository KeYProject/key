// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.DependencyContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * The proof obligation for dependency contracts. 
 */
public final class DependencyContractPO extends AbstractPO 
                                        implements ContractPO {
    
    private Term mbyAtPre;    
           
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public DependencyContractPO(InitConfig initConfig, 
	    			DependencyContract contract) {
    	super(initConfig, contract.getName(), contract);
    	assert !(contract instanceof FunctionalOperationContract);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------    
    
    private Term buildFreePre(ProgramVariable selfVar,
	                      KeYJavaType selfKJT,
	                      ImmutableList<ProgramVariable> paramVars,
	                      Term anonHeap) 
    		throws ProofInputException {
        //"self != null"
	final Term selfNotNull 
            = selfVar == null
              ? TB.tt()
              : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
              
        //"self.<created> = TRUE"
        final Term selfCreated
           = selfVar == null
             ? TB.tt()
             : TB.created(services, TB.var(selfVar));
	
        	      
        //"MyClass::exactInstance(self) = TRUE"
        final Term selfExactType
           = selfVar == null
             ? TB.tt()
             : TB.exactInstance(services, 
        	                selfKJT.getSort(), 
        	                TB.var(selfVar));
             
	
        //conjunction of... 
        //- "p_i.<created> = TRUE | p_i = null" for object parameters, and
        //- "inBounds(p_i)" for integer parameters
        Term paramsOK = TB.tt();
        for(ProgramVariable paramVar : paramVars) {
            paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
        }
        
        //initial value of measured_by clause
        final Term mbyAtPreDef;
        if(contract.hasMby()) {
            final Function mbyAtPreFunc
            	= new Function(new Name(TB.newName(services, "mbyAtPre")), 
        		       services.getTypeConverter()
        		               .getIntegerLDT()
        		               .targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }        
             
        return TB.and(new Term[]{TB.wellFormedHeap(services), 
        			 TB.wellFormed(services, anonHeap),
        	       		 selfNotNull,
        	       		 selfCreated,
        	       		 selfExactType,
        	       		 paramsOK,
        	       		 mbyAtPreDef});        
    }    
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    
    @Override
    public void readProblem() throws ProofInputException {
	ObserverFunction target = contract.getTarget();
	if(target instanceof ProgramMethod) {
	    target = javaInfo.getToplevelPM(contract.getKJT(), 
		    			    (ProgramMethod)target);
	    // FIXME: for some reason the above method call returns null now and then, the following line (hopefully) is a work-around
	    if (target == null) target = contract.getTarget();
	}
	
	//prepare variables
	final ProgramVariable selfVar 
		= TB.selfVar(services, contract.getKJT(), true);
	final ImmutableList<ProgramVariable> paramVars
		= TB.paramVars(services, target, true);

	//prepare anon heap
	final Name anonHeapName 
		= new Name(TB.newName(services, "anonHeap"));
	final Function anonHeapFunc = new Function(anonHeapName,
		heapLDT.targetSort());
	final Term anonHeap = TB.func(anonHeapFunc);
	
        //register the variables and anon heap so they are declared in proof 
	//header if the proof is saved to a file
        register(selfVar);	
        register(paramVars);
        register(anonHeapFunc);	
	
	//translate contract
	final Term pre = TB.and(buildFreePre(selfVar, 
			                     contract.getKJT(), 
					     paramVars,
					     anonHeap),
			        contract.getPre(selfVar, paramVars, services));
	final Term dep = getContract().getDep(selfVar, paramVars, services);
	
	//prepare update
	final Term changedHeap 
		= TB.anon(services, 
			  TB.heap(services), 
			  TB.setMinus(services, 
				      TB.allLocs(services), 
				      dep), 
                          anonHeap);
	final Term update = TB.elementary(services, 
					  heapLDT.getHeap(), 
					  changedHeap);
	
	//prepare target term
	final Term[] subs
		= new Term[paramVars.size() + (target.isStatic() ? 1 : 2)];
	subs[0] = TB.heap(services);
	int offset = 1;
	if(!target.isStatic()) {
	    subs[1] = TB.var(selfVar);
	    offset++;
	}
	for(ProgramVariable paramVar : paramVars) {
	    subs[offset] = TB.var(paramVar);
	    subs[offset] = TB.var(paramVar);
	    offset++;
	}
	final Term targetTerm = TB.func(target, subs);
	
	//build po
	final Term po = TB.imp(pre,
                               TB.equals(targetTerm, 
                        	         TB.apply(update, targetTerm)));
	
        //save in field
        assignPOTerms(po);
        
        //add axioms
        collectClassAxioms(contract.getKJT());
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof DependencyContractPO)) {
            return false;
        }
        DependencyContractPO cPO = (DependencyContractPO) po;
        return contract.equals(cPO.contract);
    }
    
    
    @Override
    public DependencyContract getContract() {
        return (DependencyContract)contract;
    }
    
    
    @Override
    public Term getMbyAtPre() {
	return mbyAtPre;
    }
   
    
    @Override
    public boolean equals(Object o) {
	if(!(o instanceof DependencyContractPO)) {
	    return false;
	} else {
	    return contract.equals(((DependencyContractPO)o).contract);
	}
    }
    
    
    @Override
    public int hashCode() {
        return contract.hashCode();
    }

}
