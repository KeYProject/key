// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

/** this class implements the interface for
 * MetaAdderators. MetaAdderators are used to do complex term
 * transformation when applying a taclet. Often these transformation
 * caanot be described with the taclet scheme (or trying to do so would
 * result in a huge number of rules)
 */
public class MetaDiv extends AbstractMetaOperator {

    public MetaDiv() {
	super(new Name("#div"), 2);
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
	return term.op() instanceof MetaDiv && term.arity()==arity();
    }

    /** 
     *  checks whether the result is consistent with the axiom div_axiom 
     */
    private boolean checkResult(BigInteger a, BigInteger b, BigInteger result) {	

	//    (gt(b,0) -> (leq(0,sub(a,mul(result,b))) & lt(sub(a,mul(result,b)),b))  ) 
	if ( b.compareTo(BigInteger.ZERO) > 0 )
	    return (( BigInteger.ZERO.compareTo(a.subtract(result.multiply(b))) <= 0 ) && 
		    ( a.subtract(result.multiply(b)).compareTo(b) < 0));

	//    ( lt(b,0) -> (leq(0,sub(a,mul(result,b))) & lt(sub(a,mul(result,b)),neg(b)))  ) 
	if ( b.compareTo(BigInteger.ZERO) < 0 )
	    return (( BigInteger.ZERO.compareTo(a.subtract(result.multiply(b))) <= 0 ) && 
		    ( a.subtract(result.multiply(b)).compareTo(b.negate()) < 0));
	
	return false;
    }


    /** calculates the resulting term. */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	Term arg1 = term.sub(0);
	Term arg2 = term.sub(1);
	BigInteger bigIntArg1=null;
	BigInteger bigIntArg2=null;

	bigIntArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	bigIntArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));
	if (bigIntArg2.compareTo(new BigInteger("0"))==0) {
	    Name undefName = new Name("undef("+term+")");
	    Function undef = (Function)(services.getTypeConverter().getIntegerLDT().
					functions().lookup(undefName));
	    if (undef==null) {
		undef = new RigidFunction(undefName,
				     services.getTypeConverter().
				     getIntegerLDT().targetSort(), 
				     new Sort[0]);
		services.getTypeConverter().
		    getIntegerLDT().addFunction(undef);
	    }
	    return termFactory.createFunctionTerm(undef);
	}
	BigInteger remainder = bigIntArg1.remainder(bigIntArg2);
	BigInteger bigIntResult = bigIntArg1.divide(bigIntArg2);
	if (remainder.compareTo(BigInteger.ZERO) != 0) {
	    if (bigIntArg1.compareTo(BigInteger.ZERO)<0)
		if (bigIntArg2.compareTo(BigInteger.ZERO)>0)
		    bigIntResult = bigIntResult.subtract(BigInteger.ONE);
		else
		    bigIntResult = bigIntResult.add(BigInteger.ONE);
	}
	IntLiteral lit = new IntLiteral(bigIntResult.toString());
	Debug.assertTrue(checkResult(bigIntArg1, bigIntArg2, bigIntResult), 
			 bigIntArg1+"/"+bigIntArg2+"="+bigIntResult+
			 " is inconsistent with the taclet div_axiom");
	return services.getTypeConverter().convertToLogicElement(lit);

    }

}
