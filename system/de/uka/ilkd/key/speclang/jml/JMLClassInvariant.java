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

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.AbstractClassInvariant;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;


public class JMLClassInvariant extends AbstractClassInvariant  {
    private final String originalInv;
  
  
    public JMLClassInvariant(ModelClass modelClass, 
	  		     String originalInv) {
        super(modelClass);
        this.originalInv = originalInv;
    }
  
  
    public FormulaWithAxioms getInv(Services services) {
        Sort sort = getKJT(services).getSort();
        String name = sort.name().toString().substring(0, 0).toLowerCase();
        LogicVariable selfVar = new LogicVariable(new Name(name), sort);

        FormulaWithAxioms inv 
      	    = services.getJMLTranslator().translateInv(originalInv, selfVar);
            
        return new FormulaWithAxioms(tb.all(selfVar, inv.getFormula()), 
	       			     inv.getAxioms());
    }
  
  
    public FormulaWithAxioms getOpenInv(ParsableVariable selfVar, 
	        			Services services) {
	return services.getJMLTranslator().translateInv(originalInv, selfVar);
    }
    
    
    public String toString() {
	return originalInv;
    }
    
    
    public boolean equals(Object o) {
	if(!(o instanceof JMLClassInvariant)) {
	    return false;
	}
	return originalInv.equals(((JMLClassInvariant)o).originalInv);
    }
    
    
    public int hashCode() {
	return originalInv.hashCode();
    }
}
