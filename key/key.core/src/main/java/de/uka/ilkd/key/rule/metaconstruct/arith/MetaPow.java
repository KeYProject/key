package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * Computes the pow function for literals. Computation fails if second argument is negative
 * or exceeds Integer.MAX_VALUE (the latter due to restrictions of class BigInteger).
 * 
 */
public final class MetaPow extends AbstractTermTransformer {

    public MetaPow() {
	super(new Name("#pow"), 2);
    }

    /** calculates the resulting term. */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
    	Term arg1 = term.sub(0);
    	Term arg2 = term.sub(1);
    	BigInteger bigIntArg1;
    	BigInteger bigIntArg2;

        bigIntArg1 = new BigInteger(convertToDecimalString(arg1, services));
        bigIntArg2 = new BigInteger(convertToDecimalString(arg2, services));
    	
    	if (bigIntArg2.compareTo(BigInteger.ZERO) <= -1 || bigIntArg2.compareTo(MetaShift.INT_MAX_VALUE) > 1) {
    		return term;
    	}
    	
    	BigInteger result = bigIntArg1.pow(bigIntArg2.intValue());
    	
        return services.getTermBuilder().zTerm(result.toString());
    }
}