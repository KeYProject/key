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
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.AllFields;
import de.uka.ilkd.key.java.expression.operator.adt.SetMinus;
import de.uka.ilkd.key.java.expression.operator.adt.SetUnion;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;


public final class LocSetLDT extends LDT {
    
    public static final Name NAME = new Name("LocSet");    
       
    private final Function empty;
    private final Function allLocs;
    private final Function singleton;
    private final Function union;
    private final Function intersect;
    private final Function setMinus;
    private final Function infiniteUnion;
    private final Function allFields;
    private final Function allObjects;
    private final Function arrayRange;
    private final Function freshLocs;    
    private final Function elementOf;
    private final Function subset;
    private final Function disjoint;    
    private final Function createdInHeap;    
    
    
    public LocSetLDT(Services services) {
	super(NAME, services);
        empty	         = addFunction(services, "empty");
        allLocs          = addFunction(services, "allLocs");
        singleton        = addFunction(services, "singleton");
        union            = addFunction(services, "union");
        intersect        = addFunction(services, "intersect");
        setMinus         = addFunction(services, "setMinus");
        infiniteUnion    = addFunction(services, "infiniteUnion");
        allFields        = addFunction(services, "allFields");
        allObjects       = addFunction(services, "allObjects");
        arrayRange       = addFunction(services, "arrayRange");
        freshLocs        = addFunction(services, "freshLocs");
        elementOf        = addFunction(services, "elementOf");
        subset           = addFunction(services, "subset");
        disjoint         = addFunction(services, "disjoint");
        createdInHeap    = addFunction(services, "createdInHeap");
    }
    
    
    public Function getEmpty() {
	return empty;
    }
    
    
    public Function getAllLocs() {
	return allLocs;
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
    
    
    public Function getInfiniteUnion() {
	return infiniteUnion;
    }
    
    
    public Function getAllFields() {
	return allFields;
    }
    
    
    public Function getAllObjects() {
	return allObjects;
    }    

    
    public Function getArrayRange() {
	return arrayRange;
    }    
    
    
    public Function getFreshLocs() {
	return freshLocs;
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
    
    
    public Function getCreatedInHeap() {
	return createdInHeap;
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
    public Term translateLiteral(Literal lit, Services services) {
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
	    return allFields;
	}
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return f.equals(empty);
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	if(t.op().equals(empty)) {
	    return EmptySetLiteral.LOCSET;
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
