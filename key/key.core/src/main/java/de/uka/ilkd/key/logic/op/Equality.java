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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * This class defines the equality operator "=". It is a binary
 * predicate accepting arbitrary terms (sort "any") as arguments.
 * 
 * It also defines the formula equivalence operator "<->" (which
 * could alternatively be seen as a Junctor).
 */
public final class Equality extends AbstractSortedOperator {

    /** 
     * the usual 'equality' operator '='
     */
    public static final Equality EQUALS = new Equality(new Name("equals"), 
	    					       Sort.ANY);
    
    /** 
     * the usual 'equivalence' operator '<->' (be A, B formulae then
     * 'A <->  B' is true if and only if A and B have the same truth
     * value
     */ 
    public static final Equality EQV = new Equality(new Name("equiv"),
        					    Sort.FORMULA);
    
    
    private Equality(Name name, Sort targetSort){
	super(name, new Sort[]{targetSort, targetSort}, Sort.FORMULA, true);
    }
}