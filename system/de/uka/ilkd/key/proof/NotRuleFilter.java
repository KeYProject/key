// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Rule;

/**
 * Inversion of a rule filter
 */
public class NotRuleFilter implements RuleFilter {

    private final RuleFilter a;

    public NotRuleFilter ( RuleFilter p_a ) {
	a = p_a;
    }

    public boolean filter ( Rule rule ) {
	return !a.filter ( rule );
    }

    public String toString() {
	return "Not:" + a;
    }
  
}
