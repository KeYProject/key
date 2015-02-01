// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;


import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;


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

    public boolean isReadOnlyContract(Services services);

    public Term getEnsures(LocationVariable heap);

    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(LocationVariable heap,
                        ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	        Services services);

    public Term getPost(List<LocationVariable> heapContext,
                        ProgramVariable selfVar, 
	    	        ImmutableList<ProgramVariable> paramVars, 
	    	        ProgramVariable resultVar, 
	    	        ProgramVariable excVar,
	    	        Map<LocationVariable,? extends ProgramVariable> atPreVars,
	    	        Services services);
    
    /**
     * Returns the postcondition of the contract.
     */
    public Term getPost(LocationVariable heap,
                        Term heapTerm,
	                Term selfTerm, 
	    	        ImmutableList<Term> paramTerms, 
	    	        Term resultTerm, 
	    	        Term excTerm,
	    	        Map<LocationVariable,Term> atPres,
	    	        Services services);

    public Term getPost(List<LocationVariable> heapContext,
                        Map<LocationVariable,Term> heapTerms,
	                Term selfTerm, 
	    	        ImmutableList<Term> paramTerms, 
	    	        Term resultTerm, 
	    	        Term excTerm,
	    	        Map<LocationVariable,Term> atPres,
	    	        Services services);

    /**
      * Returns the model method definition for model method contracts
      */
    public Term getRepresentsAxiom(LocationVariable heap,
        ProgramVariable selfVar,
        ImmutableList<ProgramVariable> paramVars,
        ProgramVariable resultVar,
        Map<LocationVariable,? extends ProgramVariable> atPreVars,
        Services services);

    public Term getRepresentsAxiom(LocationVariable heap,
                                   Term heapTerm,
                                   Term selfTerm,
                                   ImmutableList<Term> paramTerms,
                                   Term resultTerm,
                                   Term excTerm,
                                   Map<LocationVariable,Term> atPres,
                                   Services services);

    public String getBaseName();
    public Term getPre();
    public Term getPost();
    public Term getMod();
    public Term getMby();
    public Term getSelf();
    public ImmutableList<Term> getParams();
    public Term getResult();
    public Term getExc();
    public KeYJavaType getSpecifiedIn();

    public boolean hasResultVar();
}
