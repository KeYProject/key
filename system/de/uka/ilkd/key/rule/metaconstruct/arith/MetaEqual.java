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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class MetaEqual extends AbstractMetaOperator {


    public MetaEqual() {
	super(new Name("#eq"), 2);
    }


    public Term calculate(Term term, SVInstantiations svInst, Services services) {
	Term arg1 = term.sub(0);
	Term arg2 = term.sub(1);
	BigInteger bigIntArg1=null;
	BigInteger bigIntArg2=null;

	bigIntArg1 = new
	    BigInteger(convertToDecimalString(arg1, services));
	bigIntArg2 = new
	    BigInteger(convertToDecimalString(arg2, services));

	boolean result = bigIntArg1.compareTo(bigIntArg2) == 0;
	
	if (result)
	    return TermBuilder.DF.tt();
	else
	    return TermBuilder.DF.ff();

    }
}
