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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SortDependingFunction;


public interface Sort extends Named {
    
    /**
     * Formulas are represented as "terms" of this sort.
     */
    final Sort FORMULA = new SortImpl(new Name("Formula"));
    
    /**
     * Updates are represented as "terms" of this sort.
     */
    final Sort UPDATE = new SortImpl(new Name("Update"));

    /**
     * Term labels are represented as "terms" of this sort.
     */
    final Sort TERMLABEL = new SortImpl(new Name("TermLabel"));

    /**
     * Any is a supersort of all sorts.
     */
    final Sort ANY = new SortImpl(new Name("any"));    
    
    public final Name CAST_NAME = new Name("cast");
    final Name INSTANCE_NAME = new Name("instance");
    final Name EXACT_INSTANCE_NAME = new Name("exactInstance");    
    
    
    /**
     * Returns the direct supersorts of this sort. Not supported by NullSort.
     */
    ImmutableSet<Sort> extendsSorts();
    
    /**
     * Returns the direct supersorts of this sort.
     */
    ImmutableSet<Sort> extendsSorts(Services services); 

    /**
     * Tells whether the given sort is a reflexive, transitive subsort of this 
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
    SortDependingFunction getCastSymbol(TermServices services);
    
    /**
     * returns the instanceof symbol of this Sort
     */
    SortDependingFunction getInstanceofSymbol(TermServices services);
    
    /**
     * returns the exactinstanceof symbol of this Sort
     */
    SortDependingFunction getExactInstanceofSymbol(TermServices services);

    String declarationString();
}
