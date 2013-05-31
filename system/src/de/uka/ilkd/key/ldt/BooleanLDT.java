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


package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;


/** 
 * This class inherits from LDT and implements all method that are
 * necessary to handle the primitive type boolean.
 */
public final class BooleanLDT extends LDT {
    
    public static final Name NAME = new Name("boolean");
    
    /** the boolean literals as function symbols and terms */
    private final Function bool_true;
    private final Term term_bool_true;
    private final Function bool_false;
    private final Term term_bool_false;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    

    public BooleanLDT(Services services) {
        super(NAME, services);
        
        bool_true       = addFunction(services, "TRUE");
	term_bool_true  = TermBuilder.DF.func(bool_true);
	bool_false      = addFunction(services, "FALSE");
	term_bool_false = TermBuilder.DF.func(bool_false);
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public Term getFalseTerm() {
        return term_bool_false;
    }

    
    public Term getTrueTerm() {
        return term_bool_true;
    }

    
    /**
     * returns the function representing the boolean value <tt>FALSE</tt>
     */
    public Function getFalseConst() {
        return bool_false;
    }

    
    /**
     * returns the function representing the boolean value <tt>TRUE</tt>
     */
    public Function getTrueConst() {
        return bool_true;
    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, Term[] subs, 
                Services services, ExecutionContext ec) {
	if (subs.length == 1) {
	    return isResponsible(op, subs[0], services, ec);
	} else if (subs.length == 2) {
	    return isResponsible(op, subs[0], subs[1], services, ec);	
	}
	return false;	
    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, Term left, Term right, Services services, ExecutionContext ec) {
	return false;

    }

    
    @Override
    public boolean isResponsible
	(de.uka.ilkd.key.java.expression.Operator op, Term sub, Services services, ExecutionContext ec) {
	return false;
    }

    
    @Override 
    public Term translateLiteral(Literal lit, Services services) {
	if (lit instanceof BooleanLiteral) {
	    return (((BooleanLiteral)lit).getValue() ? 
		    term_bool_true : term_bool_false);
	}
	Debug.fail("booleanLDT: Wrong literal", lit);	
	return null;
    }

    
    @Override
    public Function getFunctionFor
	(de.uka.ilkd.key.java.expression.Operator op, Services services, 
                ExecutionContext ec) {
	assert false;
	return null;
    }   


    @Override
    public boolean hasLiteralFunction(Function f) {
	return containsFunction(f) && f.arity()==0;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	if(t.op() == bool_true) {
	    return BooleanLiteral.TRUE;
	} else if(t.op() == bool_false) { 
	    return BooleanLiteral.FALSE;
	} else {
	    assert false : "BooleanLDT: Cannot convert term to program: " + t;
	    return null;
	}
    }
    
    
    @Override
    public final Type getType(Term t) {
	if(t.sort() == targetSort()) {
	    return PrimitiveType.JAVA_BOOLEAN;
	} else {
	    assert false : "BooleanLDT: Cannot get Java type for term: " + t;
	    return null;
	}
    }
} 
