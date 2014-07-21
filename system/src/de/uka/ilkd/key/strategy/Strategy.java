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

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Generic interface for evaluating the cost of
 * a RuleApp with regard to a specific strategy
 */
public interface Strategy extends Named {

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     * @return the cost of the rule application expressed as
     * a <code>RuleAppCost</code> object.
     * <code>TopRuleAppCost.INSTANCE</code> indicates
     * that the rule shall not be applied at all 
     * (it is discarded by the strategy).
     */
    RuleAppCost computeCost ( RuleApp         app,
                              PosInOccurrence pio,
                              Goal            goal );

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is
     * called immediately before a rule is really applied
     * @return true iff the rule should be applied, false otherwise
     */
    boolean isApprovedApp ( RuleApp         app,
                            PosInOccurrence pio,
                            Goal            goal );
    
    /**
     * Instantiate an incomplete <code>RuleApp</code>. This method is
     * called when the <code>AutomatedRuleApplicationManager</code>
     * comes across a rule application in which some schema variables
     * are not yet instantiated, or which is in some other way
     * incomplete. The strategy then has the opportunity to
     * return/provide a list of (more) complete rule applications by
     * feeding them into the provided
     * <code>RuleAppCostCollector</code>.
     */
    void instantiateApp ( RuleApp              app,
                          PosInOccurrence      pio,
                          Goal                 goal,
                          RuleAppCostCollector collector );
}