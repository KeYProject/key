// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this class represents a logical variable */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;

public class LogicVariable extends TermSymbol 
    implements QuantifiableVariable, ParsableVariable {

    public LogicVariable(Name name,Sort sort) {
	super(name, sort);
	if ( sort == Sort.FORMULA ) {
	    throw new RuntimeException(
		"Attempt to create logic variable of type formula");
	}
    }
    
    /** 
     * a match between two logic variables is possible if they have been assigned
     * they are same or have been assigned to the same abstract name and the sorts
     *  are equal.
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        
        if (subst == this) {
            return mc;
        }
        if (subst instanceof LogicVariable) {
            final LogicVariable lv = (LogicVariable) subst;
            if (lv.sort() == sort() && mc.renameTable().sameAbstractName(this, lv)) {
                return mc;
            }
        }
        return null;
    }
    
    /** @return arity of the Variable as int */
    public int arity() {
	return 0;
    }
    
    /** toString */
    public String toString() {
	return ""+name()+":"+sort();
    }

}
