/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.BuiltInRule;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Index for managing built-in rules such as integer decision or update simplification rule.
 */
public class BuiltInRuleIndex implements java.io.Serializable {

    /**
     *
     */
    private static final long serialVersionUID = -4399004272449882750L;
    /** list of available built-in rules */
    private ImmutableList<BuiltInRule> rules = ImmutableSLList.nil();

    /** constructs empty rule index */
    public BuiltInRuleIndex() {
    }

    /**
     * creates a new index with the given built-in-rules
     *
     * @param rules a IList<BuiltInRule> with available built-in rules
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
