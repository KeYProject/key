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

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.SimplifyIntegerRule;

/**
 * Filter that selects instances of the SimplifierIntegerRule. 
 */
public class SimplifyIntegerRuleFilter implements RuleFilter {
    
    public static final RuleFilter INSTANCE = new SimplifyIntegerRuleFilter ();
    
    private SimplifyIntegerRuleFilter () {
    }

    public boolean filter ( Rule rule ) {
        return rule instanceof SimplifyIntegerRule;
    }

}

