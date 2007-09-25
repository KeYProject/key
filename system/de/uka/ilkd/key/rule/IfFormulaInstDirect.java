// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.proof.ProofSaver;


/**
 * Instantiation of an if-formula that has to be proven by an explicit 
 * if-goal
 */

public class IfFormulaInstDirect implements IfFormulaInstantiation {

    /**
     * Simply the formula
     */ 
    private ConstrainedFormula cf;

    public IfFormulaInstDirect ( ConstrainedFormula p_cf ) {
	cf = p_cf;
    }

    /**
     * @return the cf this is pointing to
     */
    public ConstrainedFormula getConstrainedFormula () {
	return cf;
    }    

    public String toString () {
	return toString(null);
    }

    public boolean equals ( Object p_obj ) {
	if (!(p_obj instanceof IfFormulaInstDirect)) {
	    return false;
	}
	return cf.equals ( ((IfFormulaInstDirect)p_obj).cf );
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + cf.hashCode();
    	return result;
    }

    public String toString(Services services) {
        return ProofSaver.printAnything(cf.formula(), 
                services)+(cf.constraint().isBottom() ? "" : "<<"+cf.constraint());       
    }
}
