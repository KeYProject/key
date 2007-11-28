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

package de.uka.ilkd.key.speclang.ocl;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.speclang.AbstractClassInvariant;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;
import de.uka.ilkd.key.speclang.SLTranslationError;


public class OCLClassInvariant extends AbstractClassInvariant  {
    private final String originalInv;
  
  
    public OCLClassInvariant(ModelClass modelClass, String originalInv) {
	super(modelClass);
	this.originalInv = originalInv;
    }

  
    public FormulaWithAxioms getInv(Services services) throws SLTranslationError {
        Sort sort = getKJT(services).getSort();
        LogicVariable selfVar = new LogicVariable(new Name("self"), sort);

        FormulaWithAxioms inv 
      	    = services.getOCLTranslator().translateInv(originalInv, selfVar);
        
        CreatedAttributeTermFactory catf = CreatedAttributeTermFactory.INSTANCE;
        Term closedInv = catf.createCreatedNotNullQuantifierTerm(services, 
                                                                 Op.ALL, 
                                                                 selfVar, 
                                                                 inv.getFormula());
            
        return new FormulaWithAxioms(closedInv, inv.getAxioms());
    }  
  
  
    public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
	    			        Services services) throws SLTranslationError {
	return services.getOCLTranslator().translateInv(originalInv, selfVar);
    }
    
    
    public String toString() {
	return originalInv;
    }
    
    
    public boolean equals(Object o) {
	if(!(o instanceof OCLClassInvariant)) {
	    return false;
	}
	return originalInv.equals(((OCLClassInvariant)o).originalInv);
    }
    
    
    public int hashCode() {
	return originalInv.hashCode();
    }
}
