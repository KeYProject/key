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

import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * Binary feature that returns zero iff the find-formula of the concerned rule
 * app was introduced by a certain kind rule of rule (described via a
 * <code>RuleFilter</code>)
 */
public class FormulaAddedByRuleFeature extends BinaryFeature {

    private final RuleFilter filter;
    
    private FormulaAddedByRuleFeature (RuleFilter p_filter) {
        filter = p_filter;
    }

    public static Feature create (RuleFilter p_filter) {
        return new FormulaAddedByRuleFeature ( p_filter );
    }

    public boolean filter (RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final SequentFormula cfma = pos.constrainedFormula ();
        final boolean antec = pos.isInAntec ();
        
        Node node = goal.node ();
        
        while ( !node.root () ) {
            final Node par = node.parent ();
            final Sequent pseq = par.sequent ();

            if ( !( antec ? pseq.antecedent () : pseq.succedent () ).contains ( cfma ) )
                return filter.filter ( par.getAppliedRuleApp ().rule () );
            
            node = par;
        }
        
        return false;
    }

}
