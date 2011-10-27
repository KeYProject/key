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
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public interface OperationContract extends Contract {
    
    @Override
    public ProgramMethod getTarget();
    
    /**
     * Returns the modifies clause of the contract.
     */
    public Term getMod(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Services services);
    
    
    /**
     * Returns the modifies clause of the contract.
     */
    public Term getMod(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services);

    /**
     * Returns the modifies_backup clause of the contract.
     */
    public Term getBackupMod(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
                       Services services);
    
    
    /**
     * Returns the modifies_backup clause of the contract.
     */
    public Term getBackupMod(Term heapTerm,
	               Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
                       Services services);
    
}
