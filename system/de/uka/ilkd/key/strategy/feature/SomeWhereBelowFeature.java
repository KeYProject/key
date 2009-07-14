 // This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * This feature returns zero if and only if the focus of the given rule
 * application exists, is not top-level and there is a symbol somewhere above the
 * focus that is a <code>badSymbol</code>. Optionally, one can also specify that
 * zero should only be returned if a symbol above the
 * focus is <code>badSymbol</code> and the focus has a certain subterm index.
 * 
 * TODO: eliminate this class and use term features instead
 */
public abstract class SomeWhereBelowFeature extends BinaryFeature {

    protected final Object badSymbol;
    private final int index;

    protected SomeWhereBelowFeature(Object badSymbol, int index) {
        this.badSymbol = badSymbol;
        this.index = index;
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( pos == null ) return false;
        if ( pos.isTopLevel () ) return false;
	PosInOccurrence up = pos.up(); 
	while(!up.isTopLevel ()){
	    if ( isBadSymbol(up.subTerm().op() ) && (index == -1 || index == pos.getIndex ()) ){
		return true;
	    }
	    up = up.up();
	}
        return false;
    }  
    
    protected abstract boolean isBadSymbol(Operator op);
    
}
