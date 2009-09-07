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
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;


public interface Contract extends SpecificationElement {
    
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
     * Returns the KeYJavaType to which the contract belongs.
     */
    public KeYJavaType getKJT();    
    
    /**
     * Returns the contracted function symbol.
     */
    public ObserverFunction getTarget();
    
    /**
     * Tells whether the contract contains a dependency set.
     */
    public boolean hasDep();
    
    /**
     * Returns the precondition of the contract.
     */
    public Term getPre(ProgramVariable selfVar, 
	    	       ImmutableList<ProgramVariable> paramVars,
	    	       Services services);
    
    /**
     * Returns the precondition of the contract.
     */
    public Term getPre(Term selfTerm, 
	    	       ImmutableList<Term> paramTerms,
	    	       Services services);    
    
    /**
     * Returns the dependency set.
     */
    public Term getDep(ProgramVariable selfVar,
	               ImmutableList<ProgramVariable> paramVars,
	               Services services);    
        
    /**
     * Returns the dependency set.
     */
    public Term getDep(Term heapTerm,
	               Term selfTerm,
	               ImmutableList<Term> paramTerms,
	               Services services);
    
    /**
     * Returns another contract like this one but with the passed id.
     */
    public Contract setID(int id);
    
    /**
     * Returns another contract like this one, except that it refers to the 
     * passed target. 
     */
    public Contract setTarget(KeYJavaType newKJT,
	    	              ObserverFunction newTarget,
	    		      Services services);
            
    /**
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);
}
