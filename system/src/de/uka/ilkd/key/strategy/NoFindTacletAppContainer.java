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


package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Instances of this class are immutable
 */
public class NoFindTacletAppContainer extends TacletAppContainer {

    /**
     * @param p_app
     * @param p_cost
     */
    NoFindTacletAppContainer( RuleApp p_app, RuleAppCost p_cost, long p_age ) {
        super( p_app, p_cost, p_age );
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. always true since NoFindTaclets are not bound to a find-position
     * (if-formulas are not considered)
     */
    protected boolean isStillApplicable(Goal p_goal) {
    	return true;
    }

}
