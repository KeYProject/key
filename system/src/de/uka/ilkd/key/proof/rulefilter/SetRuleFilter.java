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

import java.util.HashSet;

import de.uka.ilkd.key.rule.Rule;

/**
 * Rule filter that selects taclets which are members of a given explicit set
 */
public class SetRuleFilter implements RuleFilter {

    private HashSet<Rule> set = new HashSet<Rule> (2000);

    public void addRuleToSet ( Rule rule ) {
    	set.add(rule);
    }

    public boolean filter( Rule rule ) {
        return set.contains ( rule );
    }
}
