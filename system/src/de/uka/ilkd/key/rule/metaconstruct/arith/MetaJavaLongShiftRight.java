// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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


public final class MetaJavaLongShiftRight extends AbstractTermTransformer {

    public MetaJavaLongShiftRight() {
	super(new Name("#JavaLongShiftRight"), 2);
    }


    public Term transform(Term term, SVInstantiations svInst, Services services) {
	Term arg1 = term.sub(0);
	Term arg2 = term.sub(1);
	BigInteger intArg1;
	BigInteger intArg2;

	intArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	intArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));
	Long longResult = Long.valueOf(intArg1.longValue() >> intArg2.longValue());
	
	IntLiteral lit = new IntLiteral(longResult.toString());
	return services.getTypeConverter().convertToLogicElement(lit);
    }
}
