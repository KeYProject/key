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

import de.uka.ilkd.key.rule.ListOfBuiltInRule;
import de.uka.ilkd.key.rule.SLListOfBuiltInRule;

/**
 * Index for managing built-in-rules usch as integer decision or update
 * simplification rule.
 */
public class BuiltInRuleIndex implements java.io.Serializable {

    /** list of available built in rules */
    private ListOfBuiltInRule rules = SLListOfBuiltInRule.EMPTY_LIST;

    /** constructs empty rule index */
    public BuiltInRuleIndex() {
    }

    /**
     * creates a new index with the given built-in-rules
     * @param rules a ListOfBuiltInRule with available built in rules
     */
    public BuiltInRuleIndex(ListOfBuiltInRule rules) {
	this.rules = rules;
    }

    /**
     * returns all available rules     
     */
    public ListOfBuiltInRule rules() {
	return rules;
    }
    
    /** 
     * returns a copy of itself 
     */
    public BuiltInRuleIndex copy() {	
	return this;
    }

}
 
