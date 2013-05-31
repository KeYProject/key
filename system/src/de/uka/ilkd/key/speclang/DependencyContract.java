// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A contract about the dependencies of an observer symbol, consisting of 
 * a precondition, a depends clause, and a measured-by clause.
 */
public interface DependencyContract extends Contract {
    
    /**
     * Returns the dependency set of the contract.
     */
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services);    
        
    /**
     * Returns the dependency set of the contract.
     */
    public Term getDep(Term heapTerm,
	               Term selfTerm,
	               ImmutableList<Term> paramTerms,
	               Services services);
}
