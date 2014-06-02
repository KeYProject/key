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
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.expression.operator.adt.SeqReverse;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSub;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


public final class SeqLDT extends LDT {
    
    public static final Name NAME = new Name("Seq");    

    //getters
    private final SortDependingFunction seqGet;
    private final Function seqLen;
    private final Function seqIndexOf; 
    
    //constructors
    private final Function seqEmpty;
    private final Function seqSingleton;
    private final Function seqConcat;
    private final Function seqSub;
    private final Function seqReverse;   
    private final Function seqDef;
    private final Function values;
    
    
    public SeqLDT(TermServices services) {
	super(NAME, services);
        seqGet        = addSortDependingFunction(services, "seqGet");
        seqLen        = addFunction(services, "seqLen");
        seqEmpty      = addFunction(services, "seqEmpty");
        seqSingleton  = addFunction(services, "seqSingleton");
        seqConcat     = addFunction(services, "seqConcat");
        seqSub        = addFunction(services, "seqSub");
        seqReverse    = addFunction(services, "seqReverse");
        seqIndexOf    = addFunction(services, "seqIndexOf");
        seqDef         = addFunction(services, "seqDef");
        values			= addFunction(services, "values");
    }
    
    
    public Function getSeqGet(Sort instanceSort, TermServices services) {
	return seqGet.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getSeqLen() {
	return seqLen;
    }    
    
    
    public Function getSeqEmpty() {
	return seqEmpty;
    }
    
    
    public Function getSeqSingleton() {
	return seqSingleton;
    }

    
    public Function getSeqConcat() {
	return seqConcat;
    }
    

    public Function getSeqSub() {
	return seqSub;
    }
    
    
    public Function getSeqReverse() {
	return seqReverse;
    }

    
    public Function getSeqDef() {
	return seqDef;
    }
    
    /** Placeholder for the sequence of values observed through the execution of an enhanced for loop.
     * Follows David Cok's proposal to adapt JML to Java5.
     * @return
     */
    public Function getValues(){
    	return values;
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
	    			 TermServices services, 
	    			 ExecutionContext ec) {
	return op instanceof SeqSingleton
	       || op instanceof SeqConcat
	       || op instanceof SeqSub
	       || op instanceof SeqReverse
	       || op instanceof SeqIndexOf
	       || op instanceof SeqGet
	       || op instanceof SeqLength;
    }


    @Override
    public Term translateLiteral(Literal lit, Services services) {
	assert lit instanceof EmptySeqLiteral;
	return services.getTermBuilder().func(seqEmpty);
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	if(op instanceof SeqSingleton) {
	    return seqSingleton;
	} else if(op instanceof SeqConcat) {
	    return seqConcat;
	} else if(op instanceof SeqSub) {
	    return seqSub;
	} else if(op instanceof SeqReverse) {
	    return seqReverse;
	} else if(op instanceof SeqIndexOf) {
	    return seqIndexOf;
	} else if(op instanceof SeqGet){
	    return seqGet;
	} else if(op instanceof SeqLength){
	    return seqLen;
	}
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return f.equals(seqEmpty);
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
	if(t.op().equals(seqEmpty)) {
	    return EmptySeqLiteral.INSTANCE;
	}
	assert false;
	return null;
    }
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }


    public Function getSeqIndexOf() {
	return seqIndexOf;
    }    
}