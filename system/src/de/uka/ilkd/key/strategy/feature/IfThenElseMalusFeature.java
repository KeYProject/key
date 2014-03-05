// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Feature that counts the IfThenElse operators above the focus of a rule
 * application. When operating in argument 2 or 3 (branches) of IfThenElse, a
 * malus of 1 is added; when operating in the argument 1 (condition), a bonus of
 * -1 is added.
 */
public class IfThenElseMalusFeature implements Feature {
    public static final Feature INSTANCE = new IfThenElseMalusFeature ();
    
    private IfThenElseMalusFeature () {}
    
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( pos == null ) return NumberRuleAppCost.getZeroCost();

        ServiceCaches caches = goal.proof().getServices().getCaches();
        RuleAppCost resInt = caches.getIfThenElseMalusCache().get ( pos );
        if ( resInt != null ) {
            return resInt;
        }

        int res = 0;

        final PIOPathIterator it = pos.iterator ();
        while ( true ) {
            final int ind = it.next ();
            if ( ind == -1 ) break;

            final Term t = it.getSubTerm ();
            if ( t.op () instanceof IfThenElse) res = ind != 0 ? res + 1 : res - 1;           
        }

        resInt = NumberRuleAppCost.create ( res );
        caches.getIfThenElseMalusCache().put ( pos, resInt );
        return resInt;
    }
}
