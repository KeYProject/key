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


package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Rule;

/**
 * Intersection (conjunction) of two rule filters
 */
public class AndRuleFilter implements RuleFilter {

    private final RuleFilter a;
    private final RuleFilter b;

    public AndRuleFilter ( RuleFilter p_a, RuleFilter p_b ) {
	a = p_a;
	b = p_b;
    }

    public boolean filter ( Rule rule ) {
	return a.filter ( rule ) && b.filter ( rule );
    }


    public String toString() {
	return  a + " AND " + b;
    }

}
