// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaJavaLongShiftRight extends AbstractMetaOperator {

    public MetaJavaLongShiftRight() {
	super(new Name("#JavaLongShiftRight"), 2);
    }


    /**
     * checks whether the top level structure of the given @link Term
     * is syntactically valid, given the assumption that the top level
     * operator of the term is the same as this Operator. The
     * assumption that the top level operator and the term are equal
     * is NOT checked.  
     * @return true iff the top level structure of
     * the @link Term is valid.
     */
    public boolean validTopLevel(Term term) {
	// a meta operator accepts almost everything
	return term.op() instanceof MetaJavaLongShiftRight && term.arity()==arity();
    }


    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	Term arg1 = term.sub(0);
	Term arg2 = term.sub(1);
	BigInteger intArg1=null;
	BigInteger intArg2=null;

	intArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	intArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));
	Long longResult = new Long(intArg1.longValue() >> intArg2.longValue());
	
	IntLiteral lit = new IntLiteral(longResult.toString());
	return services.getTypeConverter().convertToLogicElement(lit);

    }

}
