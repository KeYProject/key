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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort implements Sort {
    
    private final Name name;
    private final ImmutableSet<Sort> ext;    
    private final boolean isAbstract;

    
    public AbstractSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
        this.name = name;
        this.ext = ext;
        this.isAbstract = isAbstract;
    }
   

    @Override    
    public final ImmutableSet<Sort> extendsSorts() {
	return this == Sort.FORMULA || this == Sort.UPDATE || this == Sort.ANY
	       ? DefaultImmutableSet.<Sort>nil()
	       : ext.isEmpty()
	         ? ext.add(Sort.ANY)
	         : ext;
    }
    
    
    @Override
    public final ImmutableSet<Sort> extendsSorts(Services services) {
	return extendsSorts();
    }

    
    @Override    
    public final boolean extendsTrans(Sort sort) {
        if(sort == this) {
            return true;
        } else if(this == Sort.FORMULA || this == Sort.UPDATE) {
            return false;
        } else if(sort == Sort.ANY) {
            return true;
        }
        
        for(Sort superSort : extendsSorts()) {
            if(superSort == sort || superSort.extendsTrans(sort)) {
        	return true;
            }
        }
        
        return false;
    }
    

    @Override
    public final Name name() {
        return name;
    }
    
    
    @Override
    public final boolean isAbstract() {
	return isAbstract;
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
    public final String toString() {
        return name.toString();
    }

    public String declarationString() {
        return name.toString();
    }
}
