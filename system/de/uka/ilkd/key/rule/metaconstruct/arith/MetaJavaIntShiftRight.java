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
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class MetaJavaIntShiftRight extends AbstractMetaOperator {

    public MetaJavaIntShiftRight() {
	super(new Name("#JavaIntShiftRight"), 2);
    }


    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	Term arg1 = term.sub(0);
	Term arg2 = term.sub(1);
	BigInteger intArg1=null;
	BigInteger intArg2=null;

	intArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	intArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));

	Integer intResult = Integer.valueOf(intArg1.intValue() >> intArg2.longValue());
	
	IntLiteral lit = new IntLiteral(intResult.toString());
	return services.getTypeConverter().convertToLogicElement(lit);

    }
}
