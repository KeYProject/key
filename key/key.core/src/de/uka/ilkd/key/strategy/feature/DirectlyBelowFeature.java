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

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * This feature returns zero if and only if the focus of the given rule
 * application exists, is not top-level and the symbol immediately above the
 * focus is <code>badSymbol</code>. Optionally, one can also specify that
 * zero should only be returned if the symbol immediately above the
 * focus is <code>badSymbol</code> and the focus has a certain subterm index.
 * 
 * TODO: eliminate this class and use term features instead
 */
public abstract class DirectlyBelowFeature extends BinaryFeature {

    protected final Object badSymbol;
    private final int index;

    protected DirectlyBelowFeature(Object badSymbol, int index) {
        this.badSymbol = badSymbol;
        this.index = index;
    }
    
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( pos == null ) return false;
        if ( pos.isTopLevel () ) return false;
        if ( !isBadSymbol( pos.up ().subTerm ().op () ) ) return false;
        return index == -1 || index == pos.getIndex ();
    }  
    
    protected abstract boolean isBadSymbol(Operator op);
    
}