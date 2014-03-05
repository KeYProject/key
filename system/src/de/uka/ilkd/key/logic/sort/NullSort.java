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


package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;


/**
 * There is one instance of this class per proof, representing the sort "Null".
 * This sort is a subsort of all object sorts. Unfortunately, NullSort sometimes
 * has to be treated as a special case, because it cannot support the method
 * extendsSorts() (without a Services parameter) -- for this, the object would
 * have to "know" all the object sorts, but these sorts are created only after
 * the NullSort object itself has to be created; and immutability prevents us
 * from filling in this information later.
 */
public final class NullSort implements Sort  {
    
    public static final Name NAME = new Name("Null");
    
    private final Sort objectSort;
    
    private WeakReference<Services> lastServices 
    	= new WeakReference<Services>(null);
    private WeakReference<ImmutableSet<Sort>> extCache
        = new WeakReference<ImmutableSet<Sort>>(null);
    
    
    public NullSort(Sort objectSort) {
	assert objectSort != null;
	this.objectSort = objectSort;
    }
        
    
    @Override
    public Name name() {
	return NAME;
    }
    
    
    @Override
    public ImmutableSet<Sort> extendsSorts() {
	throw new UnsupportedOperationException(
		  "NullSort.extendsSorts() cannot be supported");
    }
    
    
    @Override
    public ImmutableSet<Sort> extendsSorts(Services services) {
	assert services != null;
	assert objectSort == services.getJavaInfo().objectSort();
	
	ImmutableSet<Sort> result = extCache.get();
	if(result == null || lastServices.get() != services) {
	    result = DefaultImmutableSet.<Sort>nil();

	    for(Named n : services.getNamespaces().sorts().allElements()) {
		Sort s = (Sort)n;
		if(s != this && s.extendsTrans(objectSort)) {
		    result = result.add(s);
		}
	    }
	    
	    lastServices = new WeakReference<Services>(services);
	    extCache = new WeakReference<ImmutableSet<Sort>>(result);
	}
	
	return result;
    }
    
    
    @Override
    public boolean extendsTrans(Sort sort) {
	return sort == this
	       || sort == Sort.ANY
	       || sort.extendsTrans(objectSort);
    }
    
    
    @Override
    public boolean isAbstract() {
	return false;
    }
    
    
    @Override
    public final SortDependingFunction getCastSymbol(TermServices services) {
        SortDependingFunction result
            = SortDependingFunction.getFirstInstance(CAST_NAME, services)
        			   .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }
    
    
    @Override    
    public final SortDependingFunction getInstanceofSymbol(TermServices services) {
	SortDependingFunction result
	    = SortDependingFunction.getFirstInstance(INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this; 
	return result;
    }    
    
    
    @Override
    public final SortDependingFunction getExactInstanceofSymbol(TermServices services) {
	SortDependingFunction result
            = SortDependingFunction.getFirstInstance(EXACT_INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this;
	return result;
    }
    
    
    @Override
    public final String toString() {
        return NAME.toString();
    }


    @Override
    public String declarationString() {
        // TODO Auto-generated method stub
        return null;
    }
}
