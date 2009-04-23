// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Generic interface for evaluating the cost of
 * a RuleApp with regard to a specific feature
 * (like term size, ...)
 */
public interface RuleAppFeature {

    /**
     * Evaluate the cost of a RuleApp.
     */
    public long cost ( RuleApp app, Goal goal );

}
