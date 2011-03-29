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
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A contract about the dependencies of an observer symbol, consisting of 
 * a precondition, a depends clause, and a measured-by clause.
 */
public interface InformationFlowContract extends Contract {
    
    @Override
    public InformationFlowContract setID(int id);

    @Override
    public InformationFlowContract setTarget(KeYJavaType newKJT,
	    	                        ObserverFunction newTarget,
	    	                        Services services);
    
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
    
    /**
     * Returns the parameters dependency sets of the contract.
     */
    public Term getParameterDeps(ProgramVariable selfVar,
                                 ImmutableList<ProgramVariable> paramVars,
                                 Services services);
    
    /**
     * Returns the parameters dependency sets of the contract.
     */
    public Term getParameterDeps(Term heapTerm,
                                 Term selfTerm, 
 	                         ImmutableList<Term> paramTerms,
                                 Services services);
    
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
     * Returns the declassification formula.
     */
    public Term getDeclassification(ProgramVariable selfVar,
	                            ImmutableList<ProgramVariable> paramVars,
	                            Services services);    
        
    /**
     * Returns the declassification formula.
     */
    public Term getDeclassification(Term heapTerm,
	                            Term selfTerm,
	                            ImmutableList<Term> paramTerms,
	                            Services services);
}
