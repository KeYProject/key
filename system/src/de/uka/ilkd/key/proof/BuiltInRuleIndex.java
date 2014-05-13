// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * Index for managing built-in-rules usch as integer decision or update
 * simplification rule.
 */
public class BuiltInRuleIndex implements java.io.Serializable {

    /**
     * 
     */
    private static final long serialVersionUID = -4399004272449882750L;
    /** list of available built in rules */
    private ImmutableList<BuiltInRule> rules = ImmutableSLList.<BuiltInRule>nil();

    /** constructs empty rule index */
    public BuiltInRuleIndex() {
    }

    /**
     * creates a new index with the given built-in-rules
     * @param rules a IList<BuiltInRule> with available built in rules
     */
    public BuiltInRuleIndex(ImmutableList<BuiltInRule> rules) {
	this.rules = rules;
    }

    /**
     * returns all available rules     
     */
    public ImmutableList<BuiltInRule> rules() {
	return rules;
    }
    
    /** 
     * returns a copy of itself 
     */
    public BuiltInRuleIndex copy() {	
	return this;
    }

}