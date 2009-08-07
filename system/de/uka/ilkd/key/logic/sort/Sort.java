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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.SortDependingFunction;


public interface Sort extends Named {
    
    final Sort FORMULA  = new SortImpl(new Name("Formula"));
    final Sort UPDATE   = new SortImpl(new Name("Update"));
    final Sort ANY      = new SortImpl(new Name("any"));    
    
    final Name OBJECT_REPOSITORY_NAME = new Name("<get>");
    final Name CAST_NAME = new Name("cast");
    final Name INSTANCE_NAME = new Name("instance");
    final Name EXACT_INSTANCE_NAME = new Name("exactInstance");    
    
    
    /**
     * Returns the direct supersorts of this sort. Not supported by NullSort.
     */
    SetOfSort extendsSorts();
    
    /**
     * Returns the direct supersorts of this sort.
     */
    SetOfSort extendsSorts(Services services); 

    /**
     * Tells whether the given sort is a reflexive, transitive supersort of this 
     * sort.
     */
    boolean extendsTrans(Sort s);
    
    /**
     * Tells whether this sort has no exact elements.
     */
    boolean isAbstract();
    
    /**
     * returns the cast symbol of this Sort
     */
    SortDependingFunction getCastSymbol(Services services);
    
    /**
     * returns the instanceof symbol of this Sort
     */
    SortDependingFunction getInstanceofSymbol(Services services);
    
    /**
     * returns the exactinstanceof symbol of this Sort
     */
    SortDependingFunction getExactInstanceofSymbol(Services services);
    

    /**
     * returns the object repository of this sort
     */    
    SortDependingFunction getObjectRepository(Services services);        
}
