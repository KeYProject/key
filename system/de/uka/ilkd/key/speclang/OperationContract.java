// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 * A contract about an operation, consisting of a precondition, a 
 * postcondition, a modifies clause, and a modality.
 */
public interface OperationContract extends SpecificationElement {
    
    public static final int INVALID_ID = -1;
    
    /**
     * Returns the name of the contract.
     */
    public String getName();
    
    /**
     * Returns the id number of the contract. If a contract has instances for
     * several methods (inheritance!), all instances have the same id.
     * The id is either non-negative or equal to INVALID_ID.
     */
    public int id();
    
    /**
     * Returns the ProgramMethod representing the operation to which the 
     * contract belongs.
     */
    public ProgramMethod getProgramMethod();
    
    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();
   
    /**
     * Returns the precondition of the contract.
     */
    public Term getPre(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
	    	       Services services);

    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        Term heapAtPre,
	    	        Services services);

    /**
     * Returns the modifies clause of the contract.
     */
    public Term getModifies(ProgramVariable selfVar, 
	    		    ImmutableList<ProgramVariable> paramVars,
                            Services services);
    

    /**
     * Returns the union of this contract and those in the passed array. 
     * Probably you want to use SpecificationRepository.combineContracts()
     * instead, which additionally takes care that the combined contract can be 
     * loaded later. The resulting contract has id "INVALID_ID".
     */
    public OperationContract union(OperationContract[] others, 
                                   String name, 
                                   Services services);
    
    /**
     * Returns another contract like this one but with the passed id.
     */
    public OperationContract setID(int id);
    
    /**
     * Returns another contract like this one, except that it refers to the 
     * passed program method. 
     */
    public OperationContract setProgramMethod(ProgramMethod pm,
	    			  	      Services services);
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public OperationContract addPre(Term addedPre,
	    			    ProgramVariable selfVar, 
                                    ImmutableList<ProgramVariable> paramVars,
                                    Services services);    
        
    /**
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);
}