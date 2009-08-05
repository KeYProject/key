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
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;


public final class HeapLDT extends LDT {
    
    public static final Name NAME = new Name("Heap");    
        
    public static final Name SELECT_NAME = new Name("select");
    public static final Name STORE_NAME = new Name("store");
    
    //additional sorts
    private final Sort fieldSort;    
    
    //select/store
    private final SortDependingFunction select;
    private final Function store;
    private final Function changeHeapAtLocs;    

    //location sets
    private final Function allLocs;
    private final Function allFields;
    
    //fields
    private final Function arr;
    private final Function length;
    private final Function created;
    private final Function nextToCreate;
    
    //predicates
    private final Function wellFormed;
    
    //heap pv
    private final LocationVariable heap;
    
    
    
    public HeapLDT(Namespace sorts, Namespace functions, Namespace progVars) {
	super(NAME, sorts);
        fieldSort         = (Sort) sorts.lookup(new Name("Field"));	
        select            = (SortDependingFunction) addFunction(functions, Sort.ANY + "::" + SELECT_NAME);
        store             = addFunction(functions, "store");
        changeHeapAtLocs  = addFunction(functions, "changeHeapAtLocs");
        allLocs           = addFunction(functions, "allLocs");
        allFields         = addFunction(functions, "allFields");        
        arr               = addFunction(functions, "arr");
        length            = addFunction(functions, "Array::length");
        created           = addFunction(functions, "java.lang.Object::<created>");
        nextToCreate      = addFunction(functions, "java.lang.Object::<nextToCreate>");
        wellFormed        = addFunction(functions, "wellFormed");
        heap	          = (LocationVariable) progVars.lookup(new Name("heap"));        
    }
    
    
    public Sort getFieldSort() {
	return fieldSort;
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
    

    public Function getChangeHeapAtLocs() {
	return changeHeapAtLocs;
    }    
    
    
    public Function allLocs() {
	return allLocs;
    }
    
    
    public Function allFields() {
	return allFields;
    }
    
    
    public Function getArr() {
	return arr;
    }
    
    
    public Function getLength() {
	return length;
    }
    
    
    public Function getCreated() {
	return created;
    }
    
    
    public Function getNextToCreate() {
	return nextToCreate;
    }
    
    
    public Function getWellFormed() {
	return wellFormed;
    }
    

    public LocationVariable getHeap() {
	return heap;
    }    
    
    
    public Function getFieldSymbolForPV(ProgramVariable fieldPV, 
	    				Services services) {
	assert fieldPV.isMember();	
	final Name name;
	if(fieldPV == services.getJavaInfo().getArrayLength()) {
	    return getLength();
	} else if(fieldPV.isStatic()) {
	    assert fieldPV.toString().contains("::");
	    name = new Name(fieldPV.toString());
	} else {
	    name = new Name(fieldPV.toString());
	}
	
        Function result 
            = (Function) services.getNamespaces().functions().lookup(name); 
        if(result == null) {
            result = new Function(name, 
                     	          fieldSort, 
                		  new Sort[0], 
                		  null,
                		  true);
            services.getNamespaces().functions().addSafely(result);
        } 
        
        assert result.isUnique();        
        return result;
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
