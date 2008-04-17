// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;


/**
 * This class contains the standard rules provided by a profile.
 */
public class RuleCollection {
    
    private final ListOfBuiltInRule standardBuiltInRules;
    private final RuleSource standardTaclets;

    public RuleCollection(RuleSource standardTaclets, 
            ListOfBuiltInRule standardBuiltInRules) {
        this.standardTaclets = standardTaclets;
        this.standardBuiltInRules = standardBuiltInRules;
    }       
    
    /** returns the rule source containg all taclets for this profile */
    public RuleSource getTacletBase() {
        return standardTaclets;
    }
    
    /** returns a list of all built in rules to be used */
    public ListOfBuiltInRule getStandardBuiltInRules() {
        return standardBuiltInRules;
    }
    
    /** toString */
    public String toString() {
        return "Taclets: "+standardTaclets.toString()+
        "\n BuiltIn:"+standardBuiltInRules;
    }
    
}
