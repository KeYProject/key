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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.AnyRuleSetTacletFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * This feature checks if a rule may be applied automatically. Currently this
 * does not apply to rules which are not member of any rule set.
 */
public class AutomatedRuleFeature extends BinaryTacletAppFeature {
    
    public static final Feature INSTANCE = new AutomatedRuleFeature ();

    private AutomatedRuleFeature () {}
    
    protected boolean filter ( TacletApp app, PosInOccurrence pos, Goal goal ) {
        return AnyRuleSetTacletFilter.INSTANCE.filter( app.rule () );
    }

}
