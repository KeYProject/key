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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;


/**
 * A contract about an operation, consisting of a precondition, a 
 * postcondition, a modifies clause, and a modality.
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
    public FormulaWithAxioms getPre(ProgramVariable selfVar, 
                                    ListOfProgramVariable paramVars,
                                    Services services);

    /**
     * Returns the postcondition of the contract.
     */
    public FormulaWithAxioms getPost(ProgramVariable selfVar, 
                                     ListOfProgramVariable paramVars, 
                                     ProgramVariable resultVar, 
                                     ProgramVariable excVar,
                                     Term heapAtPre,
                                     Services services);

    /**
     * Returns the modifies clause of the contract.
     */
    public Term getModifies(ProgramVariable selfVar, 
                            ListOfProgramVariable paramVars,
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
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);
}
