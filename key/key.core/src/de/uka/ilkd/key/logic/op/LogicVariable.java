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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;


/**
 * The objects of this class represent logical variables,
 * used e.g. for quantification.
 */
public final class LogicVariable extends AbstractSortedOperator 
    implements QuantifiableVariable, ParsableVariable {

    public LogicVariable(Name name, Sort sort) {
	super(name, sort, true);
	assert sort != Sort.FORMULA;
	assert sort != Sort.UPDATE;
    }
    
    
    /** 
     * a match between two logic variables is possible if they have been assigned
     * they are same or have been assigned to the same abstract name and the sorts
     *  are equal.
     */
    @Override
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) {
            return mc;
        }
        if (subst instanceof LogicVariable) {
            final LogicVariable lv = (LogicVariable) subst;
            if(lv.sort() == sort() 
        	&& mc.renameTable().sameAbstractName(this, lv)) {
                return mc;
            }
        }
        return null;
    }
    
    
    @Override
    public String toString() {
	return name() + ":" + sort();
    }
}