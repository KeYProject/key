// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.speclang.ocl;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.logic.sort.AbstractNonCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.CreatedAttributeTermFactory;
import de.uka.ilkd.key.util.Debug;


/**
 * A UML association.
 */
public class Association {
    private static final TermBuilder tb = TermBuilder.DF;
    private static final CreatedAttributeTermFactory createdFactory = 
    	CreatedAttributeTermFactory.INSTANCE;
    
	private final Name name;
    private final ImmutableList<AssociationEnd> ends;
    private Function predicate;
    private Function func1;
    private Function func2;
    
    private ImmutableSet<Term> axioms;
    
    public Association(Services services, 
                       String name, 
                       ImmutableList<AssociationEnd> ends) {
        Debug.assertTrue(ends.size() >= 2);
        
        if(name == null) {
            name = "";
            Iterator<AssociationEnd> it = ends.iterator();
            while(it.hasNext()) {
                name += it.next().getRoleName() + "_";
            }
            name = name.substring(0, name.length() - 1);
        } 
        
        this.name = new Name(name);
        this.ends = ends;
        
        initialiseFunctions(services);
        buildAxioms(services);
    }
    
    
    public Association(Services services, ImmutableList<AssociationEnd> ends) {
        this(services, null, ends);
    }
    
    
    public Association(Services services, 
                       String name, 
                       AssociationEnd end1, 
                       AssociationEnd end2) {
        this(services, name, ImmutableSLList.<AssociationEnd>nil().prepend(end2)
                                                              .prepend(end1));
    }
    
    
    public Association(Services services, 
                       AssociationEnd end1, 
                       AssociationEnd end2) {
        this(services, null, end1, end2);
    }
    
    
    public Name getName() {
        return name;
    }
    
    
    public ImmutableList<AssociationEnd> getEnds() {
        return ends;
    }
    
    public ImmutableSet<Term> getAxioms() {
    	return axioms;
    }
    
    
    public String toString() {
        return name.toString();
    }
    
    
    private Sort getSort(Services services, ModelClass modelClass) {
        return services.getJavaInfo()
                       .getKeYJavaType(modelClass.getFullClassName()).getSort();
    }
    
    
    private void initialiseFunctions(Services services) {

        Sort[] argSorts = new Sort[ends.size()];
        Iterator<AssociationEnd> it = ends.iterator();
        int i = 0;
        while(it.hasNext()) {
            argSorts[i++] = getSort(services, it.next().getModelClass());
        }
        predicate = new NonRigidFunction(name, Sort.FORMULA, argSorts);
        services.getNamespaces().functions().add(predicate);
        
        if (ends.size() == 2) {
            AssociationEnd end1 = ends.head();
            AssociationEnd end2 = ends.tail().head();
            Sort sort1 = getSort(services, end1.getModelClass());
            Sort sort2 = getSort(services, end2.getModelClass());
            
            //TODO: if there is a qualifier <<ordered>> then SequenceSort
            //      instead of SetSort has to be used.
            Sort resSort1 = sort1;
            Sort resSort2 = sort2;
            if (ends.head().getMultiplicity().getMax() != 1) {
                resSort1 = ((AbstractNonCollectionSort) sort1).getSetSort();
            }
            if (ends.tail().head().getMultiplicity().getMax() != 1) {
                resSort2 = ((AbstractNonCollectionSort) sort2).getSetSort();
            }
            func1 = new NonRigidFunction(end2.getRoleName(), 
                                         resSort2,
                                         new Sort[] {sort1});
            func2 = new NonRigidFunction(end1.getRoleName(),
                                         resSort1,
                                         new Sort[] {sort2});
            services.getNamespaces().functions().add(func1);
            services.getNamespaces().functions().add(func2);
        }
    }
    
    
    private void buildAxioms(Services services) {
    	axioms = DefaultImmutableSet.<Term>nil();
    	
		Function inc1 = (Function) services.getNamespaces().functions().lookup(new Name(func1.sort()+"::includes"));
		Function inc2 = (Function) services.getNamespaces().functions().lookup(new Name(func2.sort()+"::includes"));

		LogicVariable a1;
		LogicVariable a2;
		
		Term a2InFunc1;
		Term a1InFunc2;
		
		if (func1.sort() instanceof AbstractCollectionSort &
    			func2.sort() instanceof AbstractCollectionSort) {
    		a1 = new LogicVariable(
    				new Name("a1"),
    				((AbstractCollectionSort)func1.sort()).elementSort());
    		a2 = new LogicVariable(
    				new Name("a2"),
    				((AbstractCollectionSort)func2.sort()).elementSort());
    		
    		a2InFunc1 = tb.func(inc1,tb.func(func1,tb.var(a2)),tb.var(a1));
    		a1InFunc2 = tb.func(inc2,tb.func(func2,tb.var(a1)),tb.var(a2));
    	}

		else if (func1.sort() instanceof AbstractCollectionSort &
    			func2.sort() instanceof AbstractNonCollectionSort) {
    		a1 = new LogicVariable(
    				new Name("a1"),
    				((AbstractCollectionSort)func1.sort()).elementSort());
    		a2 = new LogicVariable(
    				new Name("a2"),
    				func2.sort());
    		
    		a2InFunc1 = tb.func(inc1,tb.func(func1,tb.var(a2)),tb.var(a1));
    		a1InFunc2 = tb.equals(tb.func(func2,tb.var(a1)),tb.var(a2));
    	}
    	
		else if (func1.sort() instanceof AbstractNonCollectionSort &
    			func2.sort() instanceof AbstractCollectionSort) {
    		a1 = new LogicVariable(
    				new Name("a1"),
    				func1.sort());
    		a2 = new LogicVariable(
    				new Name("a2"),
    				((AbstractCollectionSort)func2.sort()).elementSort());
    		
    		a2InFunc1 = tb.equals(tb.func(func1,tb.var(a2)),tb.var(a1));
    		a1InFunc2 = tb.func(inc2,tb.func(func2,tb.var(a1)),tb.var(a2));
    	}

		else {
    		a1 = new LogicVariable(
    				new Name("a1"),
    				func1.sort());
    		a2 = new LogicVariable(
    				new Name("a2"),
    				func2.sort());
    		
    		a2InFunc1 = tb.equals(tb.func(func1,tb.var(a2)),tb.var(a1));
    		a1InFunc2 = tb.equals(tb.func(func2,tb.var(a1)),tb.var(a2));
    	}

    	Term predTerm;
    	
		if(predicate.argSort(0)==a1.sort()) {
    	    predTerm = tb.func(predicate,tb.var(a1),tb.var(a2));
		} else {
			predTerm = tb.func(predicate,tb.var(a2),tb.var(a1));
		}
		//Axiom defining relation between func1 and func2
        	
		Term axiom = createdFactory.createCreatedNotNullQuantifierTerm(
				services,
				Op.ALL,
				new LogicVariable[] {a1,a2},
				tb.equiv(a2InFunc1,a1InFunc2));
		
		axioms = axioms.add(axiom);
		
		// Axiom defining relation between func1 and pred
		
		axiom = createdFactory.createCreatedNotNullQuantifierTerm(
				services,
				Op.ALL,
				new LogicVariable[] {a1,a2},
				tb.equiv(a2InFunc1,predTerm));
		
		axioms = axioms.add(axiom);
		
		// Axiom defining relation between func2 and pred
		
		axiom = createdFactory.createCreatedNotNullQuantifierTerm(
				services,
				Op.ALL,
				new LogicVariable[] {a1,a2},
				tb.equiv(a1InFunc2,predTerm));
		
		axioms = axioms.add(axiom);
    		
    }
    
    public Function getPredicate() {
        return predicate;
    }
    
    
    public Function getFunction1() {
        return func1;
    }
    
    
    public Function getFunction2() {
        return func2;
    }
}
