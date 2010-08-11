// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.assistant;

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * A rule event has happend. The corresponding rule application object
 * is encapsulated by the input object and can be evaluated by the
 * proof assistant AI.
 */
public class RuleEventInput implements AIInput {

    /** the rule application to be evaluated */
    private final RuleApp ruleApp;

    public RuleEventInput(RuleApp app) {
	this.ruleApp = app;
    }

    /** returns the rule application */
    public RuleApp getRuleApp() {
	return ruleApp;
    }

    /** return the rule */
    public Rule getRule() {
	return ruleApp.rule();
    }

    /** 
     * returns the AI input identifier 
     */
    public int getInputID() {
	return RULE_APPLICATION_EVENT;
    }

    /** toString */
    public String toString() {
	return "RuleEvent: "+getInputID()+
	    "\n for Rule Application:"+getRuleApp();
    }

    

}
