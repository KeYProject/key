// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.util.*;

import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.YicesSolver;
import de.uka.ilkd.key.smt.Z3Solver;

/** This class encapsulates the information which 
 *  decision procedure should be used.
 */
public class DecisionProcedureSettings implements Settings {
    
    /** String used in the Settings to store the active rule */
    private static final String ACTIVE_RULE  = "[DecisionProcedure]ActiveRule";
    
    private static final String TIMEOUT="[DecisionProcedure]Timeout";
    
    /** the list of registered SettingListener */
    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();

    /** the list of available SMTRules */
    private ArrayList<SMTRule> rules = new ArrayList<SMTRule>();
    {
	//Load the available Solver
	// Rules should not be created here! USe Profiles for this purpose %%RB
	rules = new ArrayList<SMTRule>();
	rules.add(new SMTRule(new SimplifySolver()));
	rules.add(new SMTRule(new Z3Solver()));
	rules.add(new SMTRule(new YicesSolver()));
		
    }
    
    /** the currently active rule */
    private SMTRule activeRule;
    
    
    private int timeout = 60;
    
    private static DecisionProcedureSettings instance;
    
    /**
     * This is a singleton.
     */
    private DecisionProcedureSettings() {
	super();
    }
    
    public static DecisionProcedureSettings getInstance() {
	if (instance == null) {
	    instance = new DecisionProcedureSettings();
	}
	
	return instance;
    }
    
    
    /**
     * Returns a list of all available rules
     */
    public List<SMTRule> getAvailableRules() {
	return Collections.unmodifiableList(rules);
    }
    
    /**
     * returns the active rule
     * @return the active rule
     */
    public SMTRule getActiveRule() {
	return activeRule;
    }
    
    /**
     * if the specified rule is known it is set as active rule, specifying <code>null</code>
     * deactivatees the rule. Otherwise false is returned. 
     * @param r the Rule to be used for external prover invocation
     */
    public boolean setActiveRule(Rule r) {
	if (rules.contains(r)) {
	    if (r != activeRule) {
		this.activeRule = (SMTRule) r;
		fireSettingsChanged();
	    }
	    return true;
	}
	return false;
    }
    
    /**
     * sets the timeout until an external prover is terminated
     * @param t the timeout in seconds
     */
    public void setTimeout(int t) {
	if (t > 0 && t != timeout) {
	    this.timeout = t;
	    this.fireSettingsChanged();
	}
    }
    
    /**
     * returns the timeout specifying the maximal amount of time an external prover
     * is run
     * @return the timeout in seconds
     */
    public int getTimeout() {
	return this.timeout;
    }

    /**
     * true, if the argument should be used for test
     * TODO implement
     */
    public boolean useRuleForTest(int arg) {
	return true;
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	
	String ruleString = props.getProperty(ACTIVE_RULE);
	this.activeRule = null;
	
	if(ruleString != null) {
	    this.activeRule = findRuleByName(ruleString);
	}
	
	String timeoutstring = props.getProperty(TIMEOUT);
	if (timeoutstring != null) {
	    int curr = Integer.parseInt(timeoutstring);
	    if (curr > 0) {
		this.timeout = curr;
	    }
	}
    }


    /**
     * retrieves the rule of the specified name or returns <code>null</code> if
     * no such rule exists
     * @param ruleName the String unambiguously specifying a rule 
     * @return the found SMTRule or <code>null</code> 
     */
    public SMTRule findRuleByName(String ruleName) {
	for (SMTRule r : rules) {	    
	    if (r.name().toString().equals(ruleName)) {
		return r;
	    }
	}
	return null;
    }

    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
        props.setProperty(ACTIVE_RULE, "" + (activeRule == null ? "N/A" : 
            activeRule.name()));
        props.setProperty(TIMEOUT, "" + this.timeout);
    }
    

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        Iterator<SettingsListener> it = listenerList.iterator();
        while (it.hasNext()) {	    
            it.next().settingsChanged(new GUIEvent(this));
        }
    }

    
    
    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    /**
     * removes the specified listener form the listener list
     * @param l the listener
     */
    public void removeSettingsListener(SettingsListener l) {
	listenerList.remove(l);
    }

}
