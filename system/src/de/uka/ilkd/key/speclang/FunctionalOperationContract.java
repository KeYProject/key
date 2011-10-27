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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;


/**
 * A contract about an operation (i.e., a method or a constructor), consisting 
 * of a precondition, a postcondition, a modifies clause, a measured-by clause, 
 * and a modality.
 */
public interface FunctionalOperationContract extends OperationContract {
    
    /**
     * Returns the modality of the contract.
     */
    public Modality getModality();

    public Modality getPOModality();
   
    public boolean isReadOnlyContract();
    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        ProgramVariable heapAtPreVar,
	    	        ProgramVariable savedHeapAtPreVar,
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
                        Term savedHeapAtPre,
	    	        Services services);


}
