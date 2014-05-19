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

import de.uka.ilkd.key.logic.op.Operator;

/**
 * This feature returns zero if and only if the focus of the given rule
 * application exists, is not top-level and the symbol immediately above the
 * focus is <code>badSymbol</code>. Optionally, one can also specify that
 * zero should only be returned if the symbol immediately above the
 * focus is <code>badSymbol</code> and the focus has a certain subterm index.
 * 
 * TODO: eliminate this class and use term features instead
 */
public class DirectlyBelowSymbolFeature extends DirectlyBelowFeature {
   

    private DirectlyBelowSymbolFeature(Operator badSymbol, int index) {
        super(badSymbol, index);
    }

    public static Feature create(Operator badSymbol) {
        return new DirectlyBelowSymbolFeature ( badSymbol, -1 );
    }
    
    public static Feature create(Operator badSymbol, int index) {
        return new DirectlyBelowSymbolFeature ( badSymbol, index );
    }

    protected boolean isBadSymbol(Operator op) {        
        return badSymbol == op;
    }  
    
    
}