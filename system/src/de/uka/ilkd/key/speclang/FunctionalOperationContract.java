// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting 
 * of a precondition, a postcondition, a modifies clause, a measured-by clause, 
 * and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {
    
    @Override
    public FunctionalOperationContract setID(int id);
    
    @Override
    public FunctionalOperationContract setTarget(KeYJavaType newKJT,
	    	                       ObserverFunction newTarget,
	    	                       Services services);    
    
    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();
   
    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        ProgramVariable heapAtPreVar,
	    	        Services services);
    
    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(Term heapTerm,
	                Term selfTerm, 
	    	        ImmutableList<Term> paramTerms, 
	    	        Term resultTerm, 
	    	        Term excTerm,
	    	        Term heapAtPre,
	    	        Services services);

    /**
     * Returns the union of this contract and those in the passed array. 
     * Probably you want to use SpecificationRepository.combineContracts()
     * instead, which additionally takes care that the combined contract can be 
     * loaded later. The resulting contract has id "INVALID_ID".
     */
    public FunctionalOperationContract union(FunctionalOperationContract[] others, 
                                   String name, 
                                   Services services);
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public FunctionalOperationContract addPre(Term addedPre,
	    			    ProgramVariable selfVar, 
                                    ImmutableList<ProgramVariable> paramVars,
                                    Services services);    
    
    public FunctionalOperationContract setModality(Modality modality);
    public FunctionalOperationContract setModifies(Term modifies);
}
