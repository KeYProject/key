// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt.taclettranslation;

import java.util.Collection;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.Taclet;

class DefaultTacletFormula implements TacletFormula {

    Taclet taclet;
    Collection<Term> formula;
    String status;
    TacletConditions conditions;

    public TacletConditions getConditions() {
	return conditions;
    }

    public DefaultTacletFormula(Taclet taclet, Collection<Term> formula,
	    String status)  {
	this.taclet = taclet;
	this.formula = formula;
	this.status = status;
    }
    
    

    public DefaultTacletFormula(Taclet taclet, Collection<Term> formula,
	    String status, TacletConditions conditions) throws IllegalTacletException {
	super();
	this.taclet = taclet;
	this.formula = formula;
	this.status = status;
	this.conditions = conditions == null ? new TacletConditions(taclet)
	        : conditions;

    }

    public Term getFormula() {
	return TermBuilder.DF.and(formula.toArray(new Term[formula.size()]));
	// return formula;
    }

    public Taclet getTaclet() {
	return taclet;
    }

    public String getStatus() {
	return status;
    }

    public Collection<Term> getInstantiations() {

	return formula;
    }

}
