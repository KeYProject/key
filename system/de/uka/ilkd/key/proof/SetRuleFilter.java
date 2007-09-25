// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on Feb 19, 2004
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package de.uka.ilkd.key.proof;

import java.util.HashSet;

import de.uka.ilkd.key.rule.Rule;

/**
 * Rule filter that selects taclets which are members of a given explicit set 
 */
public class SetRuleFilter implements RuleFilter {

    private HashSet set = new HashSet ();

    public void addRuleToSet ( Rule rule ) {
    	set.add(rule);
    }

    public boolean filter( Rule rule ) {
        return set.contains ( rule );
    }

}
