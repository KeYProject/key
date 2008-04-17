// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Implementation of the NewRuleListener interface
 * that does nothing
 */
public class NullNewRuleListener implements NewRuleListener {

    public void ruleAdded( RuleApp        rule,
			   PosInOccurrence pos ) {
    }

    public static final NewRuleListener INSTANCE = new NullNewRuleListener();

}

