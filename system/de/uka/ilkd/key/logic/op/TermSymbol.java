// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

/**
 * The abstract class term symbol implements common features of several
 * symbols occuring as part of a term (formula). For example common getters for 
 * name and sort of the symbol. 
 */
public abstract class TermSymbol implements Operator {
    
    /** name of this symbol */
    private final Name name;
    
    /** 
     * sort of the term symbol
     */
    private final Sort sort;

    /**
     * creates a new term symbol of the given name and sort
     * @param name the Name of the symbol
     * @param sort the Sort of the symbol
     */
    protected TermSymbol(Name name, Sort sort) {
	this.name = name;
	this.sort = sort;
    }

    /** @return Sort of the TermSymbol */
    public Sort sort(Term[] term) {
	return sort;
    }

    /** @return true iff number of subterms of term is equal to its own arity
     */
    public boolean validTopLevel(Term term){
        return term.arity()==this.arity();
    }

    /** @return name of the TermSymbol */
    public Name name() {
	return name;
    }
    
    /** @return Sort of this */ 
    public Sort sort() {
	return sort;
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return term.hasRigidSubterms ();
    }
    
    /** 
     * implements the default operator matching rule which means 
     * that the compared object have to be equal otherwise
     * matching fails
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) {
            return mc;
        }
        Debug.out("Operators are different(template, candidate)", this, subst);
        return null;
    }
}
