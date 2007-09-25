//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.AbstractOperationContract;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.SLTranslationError;


public class OCLOperationContract extends AbstractOperationContract {
    private final String originalPre;
    private final String originalPost;
    private final String originalModifies;
  
  
    public OCLOperationContract(ModelMethod modelMethod,
            		        boolean terminationRequired,
	                        String originalPre,
	                        String originalPost,
	                        String originalModifies) {
        super(modelMethod, terminationRequired ? Modality.DIA : Modality.BOX);
        this.originalPre         = originalPre;
        this.originalPost        = originalPost;
        this.originalModifies    = originalModifies;
    }
  
  
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                                    ListOfParsableVariable paramVars,
                                    Services services) throws SLTranslationError {
        return services.getOCLTranslator().translatePre(originalPre, 
	       					        selfVar, 
	      					        paramVars);
    }

  
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     Services services) throws SLTranslationError {
        return services.getOCLTranslator().translatePost(originalPost, 
	        					 selfVar, 
	      					         paramVars, 
	      					         resultVar, 
	      					         excVar);
    }

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) throws SLTranslationError {
        return services.getOCLTranslator().translateModifies(originalModifies, 
	      						     selfVar, 
	      						     paramVars);
    }
}
