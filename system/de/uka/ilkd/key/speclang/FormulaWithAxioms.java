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

package de.uka.ilkd.key.speclang;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;


/**
 * Data class containing a formula and a set of axioms about the operators used 
 * in that formula (e.g. the translation of "sum" from OCL).
 */
public class FormulaWithAxioms {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    public static final FormulaWithAxioms TT = new FormulaWithAxioms(TB.tt());
    public static final FormulaWithAxioms FF = new FormulaWithAxioms(TB.ff());
    
    private final Term formula;
    private final Map<Operator, Term> axioms;
  
  
    public FormulaWithAxioms(Term formula, Map<Operator, Term> axioms) {
        this.formula = formula;
        this.axioms  = new LinkedHashMap<Operator, Term>();
        this.axioms.putAll(axioms);
    }
    
    
    public FormulaWithAxioms(Term formula) {
	this(formula, new LinkedHashMap<Operator, Term>());
    }

  
    public Term getFormula() {
        return formula;
    }

  
    public Map<Operator, Term> getAxioms() {
        Map<Operator, Term> result = new LinkedHashMap<Operator, Term>();
        result.putAll(axioms);
        return result;
    }
    
    
    public Term getAxiomsAsFormula() {
        Term result = TB.tt();
        Iterator<Term> it = axioms.values().iterator();
        while(it.hasNext()) {
            result = TB.and(result, it.next());
        }
        return result;
    }
    
    
    public FormulaWithAxioms conjoin(FormulaWithAxioms fwa) {
	FormulaWithAxioms result 
		= new FormulaWithAxioms(TB.and(formula, fwa.formula));
	result.axioms.putAll(axioms);
	result.axioms.putAll(fwa.axioms);
	return result;
    }
    
    
    public FormulaWithAxioms disjoin(FormulaWithAxioms fwa) {
	FormulaWithAxioms result 
		= new FormulaWithAxioms(TB.or(formula, fwa.formula));
	result.axioms.putAll(axioms);
	result.axioms.putAll(fwa.axioms);
	return result;
    }
    
    
    public FormulaWithAxioms imply(FormulaWithAxioms fwa) {
	FormulaWithAxioms result 
		= new FormulaWithAxioms(TB.imp(formula, fwa.formula));
	result.axioms.putAll(axioms);
	result.axioms.putAll(fwa.axioms);
	return result;
    }
    
    
    public FormulaWithAxioms negate() {
	return new FormulaWithAxioms(TB.not(formula), axioms);
    }
    
    
    public FormulaWithAxioms allClose(Services services) {
        SetOfQuantifiableVariable freeVars = formula.freeVars();
        LogicVariable[] freeVarsArray = new LogicVariable[freeVars.size()];
        IteratorOfQuantifiableVariable it = freeVars.iterator();
        for(int i = 0; i < freeVarsArray.length; i++) {
            freeVarsArray[i] = (LogicVariable) it.next();
        }
        Term closedFormula = 
         CreatedAttributeTermFactory.INSTANCE
                                    .createCreatedNotNullQuantifierTerm(
                                                services, 
                                                Op.ALL, 
                                                freeVarsArray, 
                                                formula);
        
	return new FormulaWithAxioms(closedFormula, axioms);
    }
    
    
    public boolean equals(Object o) {
	if(!(o instanceof FormulaWithAxioms)) {
	    return false;
	}
	FormulaWithAxioms fwa = (FormulaWithAxioms) o;
	return formula.equals(fwa.formula) && axioms.equals(fwa.axioms);
    }
    
    
    public int hashCode() {
	return formula.hashCode() + axioms.hashCode();
    }


    public String toString() {
	return getFormula().toString();
    }
}
