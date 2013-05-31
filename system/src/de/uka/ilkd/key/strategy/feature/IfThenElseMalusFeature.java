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

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.util.LRUCache;


/**
 * Feature that counts the IfThenElse operators above the focus of a rule
 * application. When operating in argument 2 or 3 (branches) of IfThenElse, a
 * malus of 1 is added; when operating in the argument 1 (condition), a bonus of
 * -1 is added.
 */
public class IfThenElseMalusFeature implements Feature {

    private  static LRUCache<PosInOccurrence, RuleAppCost> cache = new LRUCache<PosInOccurrence, RuleAppCost>(1000); 

    public static final Feature INSTANCE = new IfThenElseMalusFeature ();
    
    private IfThenElseMalusFeature () {}
    
    public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
        if ( pos == null ) return LongRuleAppCost.ZERO_COST;

        RuleAppCost resInt = cache.get ( pos );
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

        resInt = LongRuleAppCost.create ( res );
        cache.put ( pos, resInt );
        return resInt;
    }

    public static void clearCache(){
        cache.clear();
    }
}
