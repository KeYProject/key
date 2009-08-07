// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import java.lang.ref.WeakReference;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.SortDependingFunction;


public final class NullSort implements Sort  {
    
    public static final Name NAME = new Name("Null");
    
    private final Sort objectSort;
    
    private WeakReference<Services> lastServices 
    	= new WeakReference<Services>(null);
    private WeakReference<SetOfSort> extCache
        = new WeakReference<SetOfSort>(null);
    
    
    public NullSort(Sort objectSort) {
	assert objectSort != null;
	this.objectSort = objectSort;
    }
        
    
    @Override
    public Name name() {
	return NAME;
    }
    
    
    @Override
    public SetOfSort extendsSorts() {
	throw new UnsupportedOperationException(
		  "NullSort.extendsSorts() cannot be supported");
    }
    
    
    @Override
    public SetOfSort extendsSorts(Services services) {
	assert services != null;
	assert objectSort == services.getJavaInfo().objectSort();
	
	SetOfSort result = extCache.get();
	if(result == null || lastServices.get() != services) {
	    result = SetAsListOfSort.EMPTY_SET;

	    for(Named n : services.getNamespaces().sorts().allElements()) {
		Sort s = (Sort)n;
		if(s != this && s.extendsTrans(objectSort)) {
		    result = result.add(s);
		}
	    }
	    
	    lastServices = new WeakReference<Services>(services);
	    extCache = new WeakReference<SetOfSort>(result);
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
    public final SortDependingFunction getCastSymbol(Services services) {
        SortDependingFunction result
            = SortDependingFunction.getFirstInstance(CAST_NAME, services)
        			   .getInstanceFor(this, services);
        assert result.getSortDependingOn() == this && result.sort() == this;
        return result;
    }
    
    
    @Override    
    public final SortDependingFunction getInstanceofSymbol(Services services) {
	SortDependingFunction result
	    = SortDependingFunction.getFirstInstance(INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this; 
	return result;
    }    
    
    
    @Override
    public final SortDependingFunction getExactInstanceofSymbol(Services services) {
	SortDependingFunction result
            = SortDependingFunction.getFirstInstance(EXACT_INSTANCE_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this;
	return result;
    }
    
    
    @Override
    public final SortDependingFunction getObjectRepository(Services services) {
	SortDependingFunction result
	    = SortDependingFunction.getFirstInstance(OBJECT_REPOSITORY_NAME, services)
                                   .getInstanceFor(this, services);
	assert result.getSortDependingOn() == this && result.sort() == this;
	return result;
    } 

    
    @Override
    public final String toString() {
        return NAME.toString();
    }
}