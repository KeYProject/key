// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * ensures that the given instantiation for the schemavariable denotes
 * a static method. For determining the method the callee and the
 * arguments of the method are needed as arguments.
 */
public class TestLiteral extends VariableConditionAdapter {

    private final SchemaVariable litSV1;
    private final SchemaVariable litSV2;

    /**
     * the static reference condition checks if a suggested
     * instantiation for a schema variable denotes a static method
     * call. The flag negation allows to reuse this condition for
     * ensuring non static references.
     */
    public TestLiteral (SchemaVariable litSV1, 
			SchemaVariable litSV2) {
	this.litSV1 = litSV1;
	this.litSV2 = litSV2;
    }

    private boolean testLiteral(Term t, IntegerLDT ldt) {
	Term lit = t;
	Operator litOp = lit.op();
	while (lit.arity() == 1) {
	    if (!(litOp instanceof Function) || 
		!(lit.arity() > 0 && ldt.hasLiteralFunction((Function)litOp))) {
		return false;
	    }
	    lit = lit.sub(0);
	    litOp = lit.op();
	}
	return litOp == ldt.getNumberTerminator();
    }

    /**
     * tests if the instantiation suggestions goes along with the static
     * condition
     * @param var the template Variable to be instantiated
     * @param subst the SVSubstitute to be mapped to var
     * @param svInst the SVInstantiations that are already known to be
     * needed
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	
	final IntegerLDT ldt = services.getTypeConverter().getIntegerLDT();
	final Term lit1;
	final Term lit2;	
	if (var == litSV1) {
	    lit1 = (Term) subst;
	    lit2 = (Term) svInst.getInstantiation(litSV2);	
	} else if (var == litSV2) {
	    lit1 = (Term) svInst.getInstantiation(litSV1);
	    lit2 = (Term) subst;
	} else {
	    lit1 = (Term) svInst.getInstantiation(litSV1);
	    lit2 = (Term) svInst.getInstantiation(litSV2);	
	}
	if (lit1 == null || lit2 == null) {
	    return true;
	} else if (testLiteral(lit1, ldt) && testLiteral(lit2, ldt)) {
	    return !lit1.equals(lit2);
	}
	return false;
    }

    public String toString () {
        return "\\notSameLiteral(" + litSV1 + ", " + litSV2 + ")";
    }

}
