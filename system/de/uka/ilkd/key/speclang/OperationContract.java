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

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;


/**
 * A contract about an operation, consisting of a precondition, a 
 * postcondition, a modifies clause, and a modality.
 */
public interface OperationContract {
    public ModelMethod getModelMethod();

    public ProgramMethod getProgramMethod(Services services);
    
    public Modality getModality();
   
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                                    ListOfParsableVariable paramVars,
                                    Services services) throws SLTranslationError;

  
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     Services services) throws SLTranslationError;

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) throws SLTranslationError;
}
