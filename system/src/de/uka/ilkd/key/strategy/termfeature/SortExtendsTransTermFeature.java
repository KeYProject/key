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



package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * Term feature for testing whether the sort of a term is a subsort of a given
 * sort (or exactly the given sort).
 */
public class SortExtendsTransTermFeature extends BinaryTermFeature {
    
    private final Sort sort;

    public static TermFeature create(Sort sort) {
        return new SortExtendsTransTermFeature ( sort );
    }
    
    private SortExtendsTransTermFeature(Sort sort) {
        this.sort = sort;
    }
    
    protected boolean filter(Term term) {
        return term.sort ().extendsTrans ( sort );
    }

}
