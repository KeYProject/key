// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;


public final class Junctor extends TermSymbol {
   
    /** 
     * the true constant 
     */
    public static final Junctor TRUE = new Junctor(new Name("true"),0);

    /** 
     * the false constant 
     */
    public static final Junctor FALSE = new Junctor(new Name("false"),0);
    
    /** 
     * the ususal 'and' operator '/\' (be A, B formulae then 'A /\ B'
     * is true if and only if A is true and B is true 
     */
    public static final Junctor AND = new Junctor(new Name("and"),2);
    
    /** 
     * the ususal 'or' operator '\/' (be A, B formulae then 'A \/ B'
     * is true if and only if A is true or B is true 
     */
    public static final Junctor OR = new Junctor(new Name("or"),2);
    
    /** 
     * the ususal 'negation' operator '-' 
     */
    public static final Junctor NOT = new Junctor(new Name("not"), 1);

    /**
     * the ususal 'implication' operator '->' (be A, B formulae then
     * 'A -> B' is true if and only if A is false or B is true 
     */
    public static final Junctor IMP = new Junctor(new Name("imp"),2);

    private Junctor(Name name, int arity) {
	super(name, arity, Sort.FORMULA);
    }
   
    
    @Override
    public boolean validTopLevel(Term term){
	if(arity() != term.arity()) {
	    return false;
	}
        for(int i = 0; i < term.arity(); i++){
            if(!term.sub(i).sort().equals(Sort.FORMULA)) {
        	return false;
            }
	}
        return true;    
    }
}
