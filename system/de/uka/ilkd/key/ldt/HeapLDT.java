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
    private final Function changeHeapAtLocs2;

    //location sets
    private final Function allLocs;
    private final Function allFields;
    private final Function freshLocs;
    
    //fields
    private final Function arr;
    private final Function length;
    private final Function created;
    private final Function initialized;
    private final SortDependingFunction classPrepared;
    private final SortDependingFunction classInitialized;
    private final SortDependingFunction classInitializationInProgress;
    private final SortDependingFunction classErroneous;
    
    //null
    private final Function nullFunc;
    
    //predicates
    private final Function wellFormed;
    
    //heap pv
    private final LocationVariable heap;
    
    
    
    //-------------------------------------------------------------------------
    //constructors
    //------------------------------------------------------------------------- 
    
    public HeapLDT(Services services) {
	super(NAME, services);
	final Namespace sorts    = services.getNamespaces().sorts();
	final Namespace progVars = services.getNamespaces().programVariables();
	
        fieldSort         = (Sort) sorts.lookup(new Name("Field"));	
        select            = addSortDependingFunction(services, SELECT_NAME.toString());
        store             = addFunction(services, "store");
        changeHeapAtLocs  = addFunction(services, "changeHeapAtLocs");
        changeHeapAtLocs2 = addFunction(services, "changeHeapAtLocs2");
        allLocs           = addFunction(services, "allLocs");
        allFields         = addFunction(services, "allFields");
        freshLocs         = addFunction(services, "freshLocs");
        arr               = addFunction(services, "arr");
        length            = addFunction(services, "length");
        created           = addFunction(services, "java.lang.Object::<created>");
        initialized       = addFunction(services, "java.lang.Object::<initialized>");
        classPrepared     = addSortDependingFunction(services, "<classPrepared>");
        classInitialized  = addSortDependingFunction(services, "<classInitialized>");
        classInitializationInProgress  
                          = addSortDependingFunction(services, "<classInitializationInProgress>");
        classErroneous    = addSortDependingFunction(services, "<classErroneous>");
        nullFunc          = addFunction(services, "null");
        wellFormed        = addFunction(services, "wellFormed");
        heap	          = (LocationVariable) progVars.lookup(new Name("heap"));        
    }
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //------------------------------------------------------------------------- 
    
    private String getFieldSymbolName(LocationVariable fieldPV) {
	if(fieldPV.isImplicit()) {
	    return fieldPV.name().toString();
	} else {
	    String fieldPVName = fieldPV.name().toString();
	    int index = fieldPV.toString().indexOf("::");
	    assert index > 0;
	    return fieldPVName.substring(0, index)
	    	   + "::$" 
	    	   + fieldPVName.substring(index + 2);
	}
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public String getPrettyFieldName(Function fieldSymbol) {
	assert fieldSymbol.sort() == fieldSort;
	String name = fieldSymbol.name().toString();
	int index = name.indexOf("::");
	if(index == -1) {
	    return name;
	} else {
	    String result = name.substring(index + 2);
	    if(result.charAt(0) == '$') {
		result = result.substring(1);
	    }
	    return result;
	}
    }
    
    public String getClassName(Function fieldSymbol) {
	assert fieldSymbol.sort() == fieldSort;
	String name = fieldSymbol.name().toString();
	int index = name.indexOf("::");
	if(index == -1) {
	    return null;
	} else {
	    return name.substring(0, index);
	}
    }
    
    
    public Sort getFieldSort() {
	return fieldSort;
    }
    
    
    public Function getSelect(Sort instanceSort, Services services) {
	return select.getInstanceFor(instanceSort, services);
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
    
    
    public Function getChangeHeapAtLocs2() {
	return changeHeapAtLocs2;
    }     
    
    
    public Function allLocs() {
	return allLocs;
    }
    
    
    public Function allFields() {
	return allFields;
    }
    
    
    public Function freshLocs() {
	return freshLocs;
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
    
    
    public Function getInitialized() {
	return initialized;
    }
    
        
    public Function getClassPrepared(Sort instanceSort, Services services) {
	return classPrepared.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getClassInitialized(Sort instanceSort, Services services) {
	return classInitialized.getInstanceFor(instanceSort, services);
    }
    
    
    public Function getClassInitializationInProgress(Sort instanceSort, 
	    					     Services services) {
	return classInitializationInProgress.getInstanceFor(instanceSort, 
							    services);
    }
    
    
    public Function getClassErroneous(Sort instanceSort, Services services) {
	return classErroneous.getInstanceFor(instanceSort, services);
    }    
    
    
    public Function getNull() {
	return nullFunc;
    }
    
    
    public Function getWellFormed() {
	return wellFormed;
    }
    

    public LocationVariable getHeap() {
	return heap;
    }    
    
    
    public Function getFieldSymbolForPV(LocationVariable fieldPV, 
	    				Services services) {
	assert fieldPV.isMember();	
	if(fieldPV == services.getJavaInfo().getArrayLength()) {
	    return getLength();
	}
	
	final Name name = new Name(getFieldSymbolName(fieldPV));
	Function result = (Function) services.getNamespaces()
	                                     .functions()
	                                     .lookup(name);
	if(result == null) {
	    int index = name.toString().indexOf("::");
	    assert index > 0;
	    Name kind = new Name(name.toString().substring(index + 2));
	    
	    SortDependingFunction firstInstance 
		= SortDependingFunction.getFirstInstance(kind, services);
	    if(firstInstance != null) {
		Sort sortDependingOn = fieldPV.getContainerType().getSort();		
		result = firstInstance.getInstanceFor(sortDependingOn, services);
	    } else {
		result = new Function(name, 
				      fieldSort, 
				      new Sort[0], 
				      null,
				      true);
		services.getNamespaces().functions().addSafely(result);
	    }
	}
        
	assert result.sort() == fieldSort : "symbol has wrong sort: " + result;
        assert result.isUnique() : "symbol is not unique: " + result;        
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
    
    
    @Override
    public final Type getType(Term t) {
	assert false;
	return null;
    }    
}
