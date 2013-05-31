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



package de.uka.ilkd.key.strategy.feature.instantiator;

import de.uka.ilkd.key.rule.RuleApp;

/**
 * One branch of a <code>ChoicePoint</code>. An object of this interface will
 * be notified each time the <code>BackTrackingManager</code> decides to take
 * this branch, and can be asked for the current rule application.
 */
public interface CPBranch {
    
    /**
     * Invoked by branch manager when this branch of a choice point has been
     * chosen
     */
    void choose ();
    
    /**
     * @return the updated <code>RuleApp</code> that results when this branch
     *         of a choice point has been chosen
     */
    RuleApp getRuleAppForBranch ();
    
}
