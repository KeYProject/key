// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Walking from the root of a formula down to the focus of a rule application,
 * count how often we choose the left branch (subterm) and how the right
 * branches. This is used to identify the upper/righter/bigger summands in a
 * polynomial that is arranged in a left-associated way. 
 */
public class FindRightishFeature implements Feature {

    private final Operator add; 
    private final static RuleAppCost one = LongRuleAppCost.create ( 1 );
    
    public static Feature create(IntegerLDT numbers) {
        return new FindRightishFeature ( numbers );
    }

    private FindRightishFeature(IntegerLDT numbers) {
        add = numbers.getAdd();
    }
    
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null : "Feature is only applicable to rules with find";

        RuleAppCost res = LongRuleAppCost.ZERO_COST;
        final PIOPathIterator it = pos.iterator ();

        while ( it.next () != -1 ) {
            final Operator op = it.getSubTerm ().op ();
            final int index = it.getChild ();
            if ( index == 0 && op == add || index == 1 && op == Op.EQUALS )
                res = res.add ( one );
        }
        
        return res;
    }

    
}
