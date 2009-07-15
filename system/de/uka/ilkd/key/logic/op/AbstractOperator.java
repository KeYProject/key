// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;


/** 
 * Abstract operator class offering some common functionality.
 */
public abstract class AbstractOperator implements Operator {
    
    private final Name name;
    
    private final int arity;
   	
    
    protected AbstractOperator(Name name, int arity) {
	this.name = name;
	this.arity = arity;
    }
    
    
    @Override
    public final Name name() {
	return name;
    }
    
    
    @Override
    public final int arity() {
        return arity;
    }
    
    
    @Override
    public final Sort sort(Term[] terms) {
	return sort(new ArrayOfTerm(terms));
    }
    
    
    /** 
     * implements the default operator matching rule which means 
     * that the compared object have to be equal otherwise
     * matching fails
     */
    @Override
    public MatchConditions match(SVSubstitute subst, 
	    		         MatchConditions mc,
	    		         Services services) {
        if(subst == this) {
            return mc;
        }
        Debug.out("FAILED. Operators are different(template, candidate)", this, subst);
        return null;
    }
    
    
    @Override
    public String toString() {
	return name().toString();
    }
}
