//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;


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
                                    ListOfParsableVariable paramVars,
                                    Services services);

    /**
     * Returns the postcondition of the contract.
     * @param atPreFunctions map containing functions to use as atPre-functions.
     *                       If the method needs an atPre-function which is not
     *                       in this map, it creates a fresh one and adds it to 
     *                       the map.
     */
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     /*inout*/ Map /*Operator (normal) 
                                           -> Function (atPre)*/ atPreFunctions,
                                     Services services);

    /**
     * Returns the modifier set of the contract.
     */
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services);
    
    /**
     * Returns the contract in pretty HTML format.
     */
    public String getHTMLText(Services services);
}
