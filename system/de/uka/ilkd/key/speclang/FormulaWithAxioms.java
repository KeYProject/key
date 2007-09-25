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

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


public class FormulaWithAxioms {
    private final Term formula;
    private final Map /*Operator -> Term*/ axioms;
  
  
    public FormulaWithAxioms(Term formula, Map /*Operator -> Term*/ axioms) {
        assert formula.sort() == Sort.FORMULA;
        this.formula = formula;
        this.axioms  = new HashMap();
        this.axioms.putAll(axioms);        
    }
    
    
    public FormulaWithAxioms(Term formula) {
	this(formula, new HashMap());
    }

  
    public Term getFormula() {
        return formula;
    }

  
    public Map /*Operator -> Term*/ getAxioms() {
        HashMap result = new HashMap();
        result.putAll(axioms);
        return result;
    }
}
