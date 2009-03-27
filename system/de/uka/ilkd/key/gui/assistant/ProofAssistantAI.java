// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
package de.uka.ilkd.key.gui.assistant;

import javax.swing.AbstractButton;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * The proof assistant AI receives input descriptions {@link AIInput}
 * from the {@link ProofAssistantController}. These descriptions are
 * analyzed, an action {@link AIAction} is chosen and send back to the
 * controller which interprets the action. 
 */
public class ProofAssistantAI {
   

    /** 
     * dictionary of the ai 
     */
    private ProofAssistantDictionary dict;

    /**
     * action that does noting
     */
    private static final AIAction DO_NOTHING = new DoNothing();


    /**
     * creates and initializes the AI, i.e. loads the dictionary
     */
    public ProofAssistantAI() {	
	dict = new ProofAssistantDictionary();
    }

    /** 
     * analyzes the given input and decides about the action to be
     * taken
     * @param input the AIInput to be evaluated 
     * @return the action to be performed, e.g. display a text in the
     * user interface, set prover options etc.
     */
    public AIAction analyze(AIInput input) {
	AIAction action = null;
	switch (input.getInputID()) {
	case AIInput.RULE_APPLICATION_EVENT:
	    action = analyzeRuleAppEvent(((RuleEventInput)input).getRuleApp());
	    break;
 	case AIInput.TOOLBAR_EVENT:
	    action = analyzeToolBarEvent(((PressedButtonEventInput)input).
					 getPressedButton());
	    break;
  	case AIInput.MENUBAR_EVENT:
 	    action = analyzeMenuBarEvent(((PressedButtonEventInput)input).
 					 getPressedButton());
 	    break;
	default:
	    action = DO_NOTHING;
	}	

	return action;
    }


    /**
     * Analyzes and reacts on the given rule app, e.g. looks up the
     * rule name in the dictionary and sends back a hint to be displayed
     * by the proof assistent GUI
     * @param app the RuleApp to be analyzed
     * @return the action to be executed by the controller
     */
    private AIAction analyzeRuleAppEvent(RuleApp app) {	
	AIAction result = null;

	final String tip = dict.get("rules", 
				    app.rule().name().toString());
	if (tip != null) {
	    result = new DisplayTextAction(tip);
	} else {
	    result = DO_NOTHING;
	}

	return result;
    }

    /**
     * Analyzes an event emitted by the toolbar. At the moment a
     * simple action event is handed over.
     * @param button the AbstractButton that has been pressed 
     * @return the action to be executed by the controller
     */
    private AIAction analyzeToolBarEvent(AbstractButton button) {
	final String toolBar = "toolbar";
	AIAction result = DO_NOTHING;

	if ("Apply Heuristics".equals(button.getText())) {
	    result = new DisplayTextAction(""+dict.get(toolBar, "applyHeuristics"));
	} 
	else if ("Run Simplify".equals(button.getText())) {
	    result = new DisplayTextAction(""+dict.get(toolBar, "runSIMPLIFY"));
	}
	else if ("Run ICS".equals(button.getText())) {
	    result = new DisplayTextAction(""+dict.get(toolBar, "runICS"));
	} 
	else if ("Goal Back".equals(button.getText())) {
	    result = new DisplayTextAction(""+dict.get(toolBar, "goalBack"));
	} 	    
	else if (IconFactory.reuseLogo() == button.getIcon()) {
	    result = new DisplayTextAction(""+dict.get(toolBar, "reuse"));
	}

	return result;
    }

    /**
     * Called to analyze an action performed by the menu bar. 
     * @param button the Abstractbutton which has been pressed/selected
     * @return the action to be executed by the controller
     */
    private AIAction analyzeMenuBarEvent(AbstractButton button) {
	final String menuBar = "menu";
	AIAction result = DO_NOTHING;

	if ("File".equals(button.getText())) {
	    result = new DisplayTextAction(dict.get(menuBar, "file"));
	} 
	else if ("View".equals(button.getText())) {
	    result = new DisplayTextAction(dict.get(menuBar, "view"));
	}
	else if ("Proof".equals(button.getText())) {
	    result = new DisplayTextAction(dict.get(menuBar, "proof"));
	} 
	else if ("Options".equals(button.getText())) {
	    result = new DisplayTextAction(dict.get(menuBar, "options"));
	} 
	else if ("Tools".equals(button.getText())) {
	    result = new DisplayTextAction(dict.get(menuBar, "tools"));
	}

	return result;
    }


}
