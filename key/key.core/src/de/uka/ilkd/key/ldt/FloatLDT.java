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

package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;

/**
 * Complete this class if you want to add support for the Java float type.
 *
 * At the moment this class contains only stubs.
 */
public final class FloatLDT extends LDT {

    public static final Name NAME = new Name("float");

    public FloatLDT(TermServices services) {
	super(NAME, services);
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    			 Term[] subs,
	    			 Services services,
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    		         Term left,
	    		         Term right,
	    		         Services services,
	    		         ExecutionContext ec) {
	return false;
    }


    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    		         Term sub,
	    		         TermServices services,
	    		         ExecutionContext ec) {
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
	    // return skolem term
        final Function sk = new Function(new Name(""+NAME+lit),targetSort());
        return services.getTermBuilder().func(sk);
    }


    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    			   Services services,
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }


    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }


    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	return null;
    }


    @Override
    public final Type getType(Term t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_FLOAT;
	} else {
	    return null;
	}
    }
}