// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;


/**
 * A contract about an operation, consisting of a precondition, a 
 * postcondition, a modifier set, and a modality.
 */
public interface OperationContract {
    
    /**
     * Returns the unique internal name of the contract.
     */
    public String getName();
    
    /**
     * Returns the displayed name of the contract.
     */
    public String getDisplayName();
    
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
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                                    ImmutableList<ParsableVariable> paramVars,
                                    Services services);
    
    /**
     * Returns the precondition of the contract.
     */
    public FormulaWithAxioms getPre(Term self, 
                                    ImmutableList<Term> params,
                                    Services services);
    
    /**
     * Returns the precondition of the contract.
     */
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                                    ImmutableList<ParsableVariable> paramVars,
                                    Term memoryArea,
                                    Services services);
    
    /**
     * Returns the postcondition of the contract.
     * @param atPreFunctions map containing functions to use as atPre-functions.
     *                       If the method needs an atPre-function which is not
     *                       in this map, it creates a fresh one and adds it to 
     *                       the map.˙
     */
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ImmutableList<ParsableVariable> paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     /*inout*/ Map<Operator, Function/* at pre */> atPreFunctions,
                                     Services services);
    
    /**
     * Returns the postcondition of the contract.
     * @param atPreFunctions map containing functions to use as atPre-functions.
     *                       If the method needs an atPre-function which is not
     *                       in this map, it creates a fresh one and adds it to 
     *                       the map.˙
     */
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
            ImmutableList<ParsableVariable> paramVars, 
            ParsableVariable resultVar, 
            ParsableVariable excVar,
            Term memoryArea,
            /*inout*/ Map<Operator, Function/* at pre */> atPreFunctions,
            Services services);
    
    public Term getWorkingSpace(Term self, 
                ImmutableList<Term> params,
                Services services);
    
    public Term getWorkingSpace(ParsableVariable selfVar, 
                ImmutableList<ParsableVariable> paramVars,
                Services services);
    
    public FormulaWithAxioms getWorkingSpacePost(ParsableVariable selfVar, 
            ImmutableList<ParsableVariable> paramVars, 
            ParsableVariable resultVar, 
            ParsableVariable excVar,
            /*inout*/ Map<Operator, Function/* at pre */> atPreFunctions,
            Services services);

    /**
     * Returns the modifier set of the contract.
     */
    public ImmutableSet<LocationDescriptor> getModifies(ParsableVariable selfVar, 
                                               ImmutableList<ParsableVariable> paramVars,
                                               Services services);
    

    /**
     * Returns the union of this contract and those in the passed array. 
     * Probably you want to use SpecificationRepository.combineContracts()
     * instead, which additionally takes care that the combined contract can be 
     * loaded later.
     */
    public OperationContract union(OperationContract[] others, 
                                   String name, 
                                   String displayName, 
                                   Services services);
    
    /**
     * Returns another contract like this one, except that it refers to the 
     * passed program method.
     */
    public OperationContract replaceProgramMethod(ProgramMethod pm,
	    					  Services services);
    
    /**
     * Returns another contract like this one, except that the passed term
     * has been added as a precondition.
     */
    public OperationContract addPre(FormulaWithAxioms addedPre,
	    			    ParsableVariable selfVar, 
                                    ImmutableList<ParsableVariable> paramVars,
                                    Services services);
        
    /**
     * Returns the modifier set of the contract.
     */
    public ImmutableSet<LocationDescriptor> getModifies(ParsableVariable selfVar, 
                                               Term memoryArea, 
                                               ImmutableList<ParsableVariable> paramVars,
                                               Services services);
    
    /**
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);
}
