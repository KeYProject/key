// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.SLListOfRuleSet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Filter that selects taclets that belong to at least one
 * rule set, i.e. taclets that can be applied automatically.
 */
public class AnyRuleSetTacletFilter extends TacletFilter {

    private AnyRuleSetTacletFilter () {
    }

    /**
     * @return true iff <code>taclet</code> should be included in the
     * result
     */
    public boolean filter ( Taclet taclet ) {
	return !taclet.getRuleSets ().isEmpty();
    }

    public final static TacletFilter INSTANCE = new AnyRuleSetTacletFilter ();
}
