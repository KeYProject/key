// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml;

import java.util.Map;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfParsableVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.AbstractOperationContract;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;


public class JMLOperationContract extends AbstractOperationContract {
    private final String originalDiverges;
    private final boolean terminationCase;
    private final String originalRequires;
    private final String originalEnsures;
    private final String originalSignals;
    private final String originalAssignable;
  
  
    public JMLOperationContract(ModelMethod modelMethod,
            		        String originalDiverges,
          		        boolean terminationCase,
          		        String originalRequires,
          		        String originalEnsures,
            		        String originalSignals,
	                        String originalAssignable) {
	super(modelMethod, terminationCase ? Modality.DIA : Modality.BOX);
        this.originalDiverges   = originalDiverges;
        this.terminationCase    = terminationCase;
        this.originalRequires   = originalRequires;
        this.originalEnsures    = originalEnsures;
        this.originalSignals    = originalSignals;
        this.originalAssignable = originalAssignable;
    }
  
  
    public FormulaWithAxioms getPre(ParsableVariable selfVar, 
                                    ListOfParsableVariable paramVars,
                                    Services services) {
        JMLTranslator translator = services.getJMLTranslator();
        
        FormulaWithAxioms required 
        	= translator.translateRequires(originalRequires, 
        				       selfVar, 
        				       paramVars);
        Term resultFormula = required.getFormula();
        Map resultAxioms = required.getAxioms();
        resultAxioms.putAll(required.getAxioms());
        
        if(terminationCase) {
            FormulaWithAxioms diverges 
            	= translator.translateDiverges(originalDiverges, 
            				       selfVar, 
            				       paramVars);
            resultFormula = tb.and(resultFormula, tb.not(diverges.getFormula()));
            resultAxioms.putAll(diverges.getAxioms());
        }
        
        return new FormulaWithAxioms(resultFormula, resultAxioms);
    }

  
    public FormulaWithAxioms getPost(ParsableVariable selfVar, 
                                     ListOfParsableVariable paramVars, 
                                     ParsableVariable resultVar, 
                                     ParsableVariable excVar,
                                     Services services) {
	JMLTranslator translator = services.getJMLTranslator();
	
        FormulaWithAxioms ensures
	= translator.translateEnsures(originalEnsures,
			    	      selfVar,
				      paramVars,
				      resultVar,
				      excVar);
	FormulaWithAxioms signals
		= translator.translateSignals(originalSignals, 
					      selfVar, 
					      paramVars, 
					      resultVar, 
					      excVar);
        
        Term excVarTerm;
        if(excVar instanceof ProgramVariable) {
            excVarTerm = tb.var((ProgramVariable) excVar);
        } else {
            excVarTerm = tb.var((LogicVariable) excVar);
        }
        Term excNullTerm = tb.equals(excVarTerm, tb.NULL(services));

        Term resultFormula = tb.ife(excNullTerm, ensures.getFormula(), signals.getFormula());
        Map resultAxioms = ensures.getAxioms();
        resultAxioms.putAll(signals.getAxioms());
        
        return new FormulaWithAxioms(resultFormula, resultAxioms);
    }

  
    public SetOfLocationDescriptor getModifies(ParsableVariable selfVar, 
                                               ListOfParsableVariable paramVars,
                                               Services services) {
        return services.getJMLTranslator().translateAssignable(
        					     	originalAssignable, 
        					     	selfVar, 
        					     	paramVars);
    }
}
