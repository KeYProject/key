package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.Taclet;

class DefaultTacletFormula implements TacletFormula {

    Taclet taclet;
    Term   formula;
    
        
    public DefaultTacletFormula(Taclet taclet, Term formula) {
	super();
	this.taclet = taclet;
	this.formula = formula;
    }

    public Term getFormula() {
	return formula;
    }

    public Taclet getTaclet() {
	return taclet;
    }

}
