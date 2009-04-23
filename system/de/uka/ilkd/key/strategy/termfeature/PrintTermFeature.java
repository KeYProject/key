// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

public class PrintTermFeature implements TermFeature {
    
    public static final TermFeature INSTANCE = new PrintTermFeature ();
    
    private PrintTermFeature () {}
    
    public RuleAppCost compute(Term term) {
        System.out.println ( term );
        return LongRuleAppCost.ZERO_COST;
    }
}
