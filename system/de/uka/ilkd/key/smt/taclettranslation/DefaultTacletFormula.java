package de.uka.ilkd.key.smt.taclettranslation;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

class DefaultTacletFormula implements TacletFormula {

    Taclet taclet;
    Term   formula;
    String status;
    
        
    public DefaultTacletFormula(Taclet taclet, Term formula, String status) {
	super();
	this.taclet = taclet;
	this.formula = formula;
	this.status = status;
    }

    public Term getFormula() {
	return formula;
    }

    public Taclet getTaclet() {
	return taclet;
    }

    public String getStatus() {
	return status;
    }

}
