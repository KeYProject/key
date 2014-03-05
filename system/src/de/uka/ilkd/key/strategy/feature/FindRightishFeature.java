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

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Walking from the root of a formula down to the focus of a rule application,
 * count how often we choose the left branch (subterm) and how the right
 * branches. This is used to identify the upper/righter/bigger summands in a
 * polynomial that is arranged in a left-associated way. 
 */
public class FindRightishFeature implements Feature {

    private final Operator add; 
    private final static RuleAppCost one = NumberRuleAppCost.create ( 1 );
    
    public static Feature create(IntegerLDT numbers) {
        return new FindRightishFeature ( numbers );
    }

    private FindRightishFeature(IntegerLDT numbers) {
        add = numbers.getAdd();
    }
    
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null : "Feature is only applicable to rules with find";

        RuleAppCost res = NumberRuleAppCost.getZeroCost();
        final PIOPathIterator it = pos.iterator ();

        while ( it.next () != -1 ) {
            final Operator op = it.getSubTerm ().op ();
            final int index = it.getChild ();
            if ( index == 0 && op == add || index == 1 && op == Equality.EQUALS )
                res = res.add ( one );
        }
        
        return res;
    }

    
}
