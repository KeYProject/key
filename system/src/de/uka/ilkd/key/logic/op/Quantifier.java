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


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * The two objects of this class represent the universal and the existential
 * quantifier, respectively.
 */
public final class Quantifier extends AbstractSortedOperator {
    public static final Name ALL_NAME = new Name("all");
    public static final Name EX_NAME = new Name("exists");
    
    /** 
     * the ususal 'forall' operator 'all' (be A a formula then       
     * 'all x.A' is true if and only if for all elements d of the
     * universe A{x<-d} (x substitued with d) is true 
     */
    public static final Quantifier ALL = new Quantifier(ALL_NAME);
    
    /** 
     * the ususal 'exists' operator 'ex' (be A a formula then       
     * 'ex x.A' is true if and only if there is at least one elements
     * d of the universe such that A{x<-d} (x substitued with d) is true 
     */     
    public static final Quantifier EX = new Quantifier(EX_NAME);


    private Quantifier(Name name) {
	super(name, 
              new Sort[]{Sort.FORMULA}, 
              Sort.FORMULA, 
              new Boolean[]{true}, 
              true);
    }
}
