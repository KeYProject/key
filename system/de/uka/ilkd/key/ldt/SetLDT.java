// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;


public final class SetLDT extends LDT {
    
    public static final Name NAME = new Name("Set");    
       
    private final Function empty;
    private final Function singleton;
    private final Function union;
    private final Function intersect;
    private final Function setMinus;
    private final Function setComprehension;
    private final Function elementOf;
    private final Function subset;
    private final Function disjoint;    
    
    public SetLDT(Services services) {
	super(NAME, services);
        empty	         = addFunction(services, "empty");
        singleton        = addFunction(services, "singleton");
        union            = addFunction(services, "union");
        intersect        = addFunction(services, "intersect");
        setMinus         = addFunction(services, "setMinus");
        setComprehension = addFunction(services, "setComprehension");
        elementOf        = addFunction(services, "elementOf");
        subset           = addFunction(services, "subset");
        disjoint         = addFunction(services, "disjoint");
    }
    
    
    public Function getEmpty() {
	return empty;
    }
    
    
    public Function getSingleton() {
	return singleton;
    }
    
    
    public Function getUnion() {
	return union;
    }
    
    
    public Function getIntersect() {
	return intersect;
    }
    
    
    public Function getSetMinus() {
	return setMinus;
    }
    
    
    public Function getSetComprehension() {
	return setComprehension;
    }
    
    
    public Function getElementOf() {
	return elementOf;
    }
    
    
    public Function getSubset() {
	return subset;
    }
    
    
    public Function getDisjoint() {
	return disjoint;
    }
    
    
    @Override
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op, 
                                 Term[] subs, 
                                 Services services, 
                                 ExecutionContext ec) {
	return isResponsible(op, (Term)null, services, ec);
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
	    			 Services services, 
	    			 ExecutionContext ec) {
	return op instanceof Singleton
	       || op instanceof SetUnion
	       || op instanceof Intersect 
	       || op instanceof SetMinus
	       || op instanceof AllFields;
    }


    @Override
    public Term translateLiteral(Literal lit) {
	assert lit instanceof EmptySetLiteral;
	return TermBuilder.DF.func(empty);
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	if(op instanceof Singleton) {
	    return singleton;
	} else if(op instanceof SetUnion) {
	    return union;
	} else if(op instanceof Intersect) {
	    return intersect;
	} else if(op instanceof SetMinus) {
	    return setMinus;
	} else if(op instanceof AllFields) {
	    return serv.getTypeConverter().getHeapLDT().allFields();
	}
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return f.equals(empty);
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children) {
	if(t.op().equals(empty)) {
	    return EmptySetLiteral.INSTANCE;
	}
	assert false;
	return null;
    }
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }    
}
