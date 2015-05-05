// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public abstract class MetaShift extends AbstractTermTransformer {

	public final static BigInteger INT_MIN_VALUE = BigInteger.valueOf(Integer.MIN_VALUE);
	public final static BigInteger INT_MAX_VALUE = BigInteger.valueOf(Integer.MAX_VALUE);


	protected MetaShift(Name name) {
		super(name, 2);
	}


	public Term transform(Term term, SVInstantiations svInst, Services services) {
		Term arg1 = term.sub(0);
		Term arg2 = term.sub(1);
		BigInteger left;
		BigInteger right;

		left = new
				BigInteger(convertToDecimalString(arg1, services));
		right = new
				BigInteger(convertToDecimalString(arg2, services));

		BigInteger result = left;
		do {

			BigInteger rightActual = right;

			if (rightActual.compareTo(INT_MIN_VALUE) <= 0 ) {
				rightActual = INT_MIN_VALUE;
			} else {
				if (rightActual.compareTo(INT_MAX_VALUE)>=0) {
					rightActual = INT_MAX_VALUE;
				}
			}			

			result = shiftOp(result, rightActual);
			
			right = right.subtract(rightActual);			

		} while ( !right.equals(BigInteger.ZERO)
				&& !result.equals(BigInteger.ZERO) // if the result is zero nothing changes anymore, so we can exit the loop 
				);

		return services.getTypeConverter().convertToLogicElement(new IntLiteral(result.toString()));

	}


	protected abstract BigInteger shiftOp(BigInteger result, BigInteger rightOp);
}