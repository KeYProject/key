// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public final class Quantifier extends AbstractSortedOperator {
    
    /** 
     * the ususal 'forall' operator 'all' (be A a formula then       
     * 'all x.A' is true if and only if for all elements d of the
     * universe A{x<-d} (x substitued with d) is true 
     */
    public static final Quantifier ALL = new Quantifier(new Name("all"));
    
    /** 
     * the ususal 'exists' operator 'ex' (be A a formula then       
     * 'ex x.A' is true if and only if there is at least one elements
     * d of the universe such that A{x<-d} (x substitued with d) is true 
     */     
    public static final Quantifier EX = new Quantifier(new Name("exist"));


    private Quantifier(Name name) {
	super(name, new Sort[]{Sort.FORMULA}, Sort.FORMULA);
    }

    
    /** @return true iff the subterm at postion 0 has Sort.FORMULA and the
     * arity of the term is 1 and at least one variable is bound.
     */
    @Override
    protected boolean additionalValidTopLevel(Term term){
	return (term.varsBoundHere(0).size() > 0);
    }
    
    
    @Override
    public boolean isRigid() {
	return true;
    }    
}
