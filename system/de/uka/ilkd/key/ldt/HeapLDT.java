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
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


public final class HeapLDT extends LDT {
    
    private static final Name NAME = new Name("Heap");
    
    private final LocationVariable heap;
    private final SortDependingFunction select;
    private final Function store;
    private final Function arr;
    private final Function wellFormed;
    private final Function changeHeapAtLocs;
    private final Sort fieldSort;
    
    
    public HeapLDT(Namespace sorts, Namespace functions, Namespace progVars) {
	super((Sort)sorts.lookup(NAME), null);
        heap	          = (LocationVariable) progVars.lookup(new Name("heap"));
        select            = (SortDependingFunction) addFunction(functions, "Null::select");
        store             = addFunction(functions, "store");
        arr               = addFunction(functions, "arr");
        wellFormed        = addFunction(functions, "wellFormed");
        changeHeapAtLocs  = addFunction(functions, "changeHeapAtLocs");
        fieldSort         = (Sort) sorts.lookup(new Name("Field"));
    }
    
    
    public LocationVariable getHeap() {
	return heap;
    }
    
    
    public Function getSelect(Sort instanceSort, Services services) {
	return (Function) select.getInstanceFor(instanceSort, services);
    }
    
    
    public Sort getSortOfSelect(Operator op) {
	if(op instanceof SortDependingFunction 
           && ((SortDependingFunction)op).isSimilar(select)) {
	   return ((SortDependingFunction)op).getSortDependingOn(); 
	} else {
	    return null;
	}
    }
    
    
    public Function getStore() {
	return store;
    }
    
    
    public Function getArr() {
	return arr;
    }
    
    
    public Function getWellFormed() {
	return wellFormed;
    }
    
    
    public Function getChangeHeapAtLocs() {
	return changeHeapAtLocs;
    }
    
    
    public Sort getFieldSort() {
	return fieldSort;
    }
    
    
    @Override
    public Name name() {
	return NAME;
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
	    			 Services services, 
	    			 ExecutionContext ec) {
	return false;
    }


    @Override
    public Term translateLiteral(Literal lit) {
	assert false;
	return null;
    }
    

    @Override
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op, 
	    			   Services serv, 
	    			   ExecutionContext ec) {
	assert false;
	return null;
    }

    
    @Override
    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    
    @Override
    public Expression translateTerm(Term t, ExtList children) {
	assert false;
	return null;
    }
}

