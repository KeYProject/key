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

package de.uka.ilkd.key.logic.sort;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;

/**
 * Abstract base class for implementations of the Sort interface.
 */
public abstract class AbstractSort implements Sort {
    
    private final Name name;
    private ImmutableSet<Sort> ext;    
    private final boolean isAbstract;
    
    public AbstractSort(Name name, ImmutableSet<Sort> ext, boolean isAbstract) {
    	this.name = name;
        this.ext = ext;
        this.isAbstract = isAbstract;
    }
   

    @Override    
    public final ImmutableSet<Sort> extendsSorts() {
        if (this == Sort.FORMULA || this == Sort.UPDATE || this == Sort.ANY) {
            return DefaultImmutableSet.<Sort>nil();
        } else {
            if (ext.isEmpty()) {
                ext = DefaultImmutableSet.<Sort>nil().add(ANY);
            } 
            return ext;
        }
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
        } else if (sort == Sort.ANY) {
            return true;
        }
        
        return extendsSorts().exists((Sort superSort)-> superSort == sort || superSort.extendsTrans(sort));
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
    public final String toString() {
        return name.toString();
    }

}