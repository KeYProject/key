/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.rule.BuiltInRule;

import org.key_project.util.collection.ImmutableList;


/**
 * This class contains the standard rules provided by a profile.
 */
public record RuleCollection(RuleSource standardTaclets,ImmutableList<BuiltInRule>standardBuiltInRules){

/**
 * returns the rule source containg all taclets for this profile
 */
public RuleSource getTacletBase(){return standardTaclets;}

/**
 * returns a list of all built in rules to be used
 */
@Override public ImmutableList<BuiltInRule>standardBuiltInRules(){return standardBuiltInRules;}

/**
 * toString
 */
public String toString(){return"Taclets: "+standardTaclets.toString()+"\n BuiltIn:"+standardBuiltInRules;}

}
