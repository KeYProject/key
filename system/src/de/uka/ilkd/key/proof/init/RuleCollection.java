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

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.rule.BuiltInRule;


/**
 * This class contains the standard rules provided by a profile.
 */
public class RuleCollection {

    private final ImmutableList<BuiltInRule> standardBuiltInRules;
    private final RuleSource standardTaclets;

    public RuleCollection(RuleSource standardTaclets,
            ImmutableList<BuiltInRule> standardBuiltInRules) {
        this.standardTaclets = standardTaclets;
        this.standardBuiltInRules = standardBuiltInRules;
    }

    /** returns the rule source containg all taclets for this profile */
    public RuleSource getTacletBase() {
        return standardTaclets;
    }

    /** returns a list of all built in rules to be used */
    public ImmutableList<BuiltInRule> getStandardBuiltInRules() {
        return standardBuiltInRules;
    }

    /** toString */
    public String toString() {
        return "Taclets: "+standardTaclets.toString()+
        "\n BuiltIn:"+standardBuiltInRules;
    }

}