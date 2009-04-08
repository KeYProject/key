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
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.smt.SMTRule;

/** This class encapsulates the information which 
 *  decision procedure should be used.
 */
public class DecisionProcedureSettings implements Settings {
    
    public static final RuleDescriptor NOT_A_RULE = 
	    new RuleDescriptor(new Name("N/A"), "N/A");
    /**
     * Small data container wrapping name and display name of a rule     
     */
    public static class RuleDescriptor {		
	
	private final Name ruleName;
	private final String displayName;
	
	public RuleDescriptor(Name ruleName, String displayName) {
	    this.ruleName    = ruleName;
	    this.displayName = displayName; 
	}
	public String getDisplayName() {
	    return displayName;
	}

	public Name getRuleName() {
	    return ruleName;
	}
	
	public boolean equals(Object o) {
	    if (o instanceof RuleDescriptor) {
		return ((RuleDescriptor) o).ruleName.equals(ruleName);
	    }
	    return false;
	}
	
	public String toString() {
	    return ruleName + "(" + displayName + ")";
	}
    }
    
    /** String used in the Settings to store the active rule */
    private static final String ACTIVE_RULE  = "[DecisionProcedure]ActiveRule";
    
    private static final String TIMEOUT="[DecisionProcedure]Timeout";

    /** the list of registered SettingListener */
    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();
    
    /** the list of available SMTRules */
    private ArrayList<RuleDescriptor> rules = new ArrayList<RuleDescriptor>();
    
    /** the currently active rule */
    private Name activeRule = NOT_A_RULE.getRuleName();
    
    private int timeout = 60;
    
    private static DecisionProcedureSettings instance;
    
    /**
     * This is a singleton.
     */
    private DecisionProcedureSettings() {
	super();
    }
    
    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }
    
    /**
     * retrieves the rule of the specified name or returns <code>null</code> if
     * no such rule exists
     * @param ruleName the String unambiguously specifying a rule 
     * @return the found SMTRule or <code>null</code> 
     */
    public RuleDescriptor findRuleByName(String ruleName) {
	for (RuleDescriptor r : rules) {	    
	    if (r.getRuleName().toString().equals(ruleName)) {
		return r;
	    }
	}
	return NOT_A_RULE;
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
    
    /**
     * returns the active rule
     * @return the active rule
     */
    public RuleDescriptor getActiveRule() {
	return findRuleByName(activeRule.toString());
    }
    
    /**
     * Returns a list of all available rules
     */
    public List<RuleDescriptor> getAvailableRules() {
	return Collections.unmodifiableList(rules);
    }
    
    /**
     * returns the timeout specifying the maximal amount of time an external prover
     * is run
     * @return the timeout in seconds
     */
    public int getTimeout() {
	return this.timeout;
    }
    
    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {	
	String ruleString = props.getProperty(ACTIVE_RULE);
	this.activeRule = new Name(ruleString);
	
	String timeoutstring = props.getProperty(TIMEOUT);
	if (timeoutstring != null) {
	    int curr = Integer.parseInt(timeoutstring);
	    if (curr > 0) {
		this.timeout = curr;
	    }
	}
    }

    /**
     * removes the specified listener form the listener list
     * @param l the listener
     */
    public void removeSettingsListener(SettingsListener l) {
	listenerList.remove(l);
    }

    /**
     * if the specified rule is known it is set as active rule, otherwise or specifying <code>null</code>
     * deactivates the rule. 
     */
    public void setActiveRule(Name ruleName) {
	final RuleDescriptor rule = ruleName == null ? 
		NOT_A_RULE : findRuleByName(ruleName.toString());
	if (rule != findRuleByName(""+activeRule)) {
	    this.activeRule = rule.getRuleName();
	    fireSettingsChanged();
	}
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
     * updates the current available SMT rules
     * @param profile the active Profile 
     */
    public void updateSMTRules(Profile profile) {
	//Load the available Solver
	// Rules should not be created here! Use Profiles for this purpose %%RB
	rules = new ArrayList<RuleDescriptor>();
	for (Rule r : profile.
		getStandardRules().getStandardBuiltInRules()) {
	    if (r instanceof SMTRule) {
		rules.add(new RuleDescriptor(r.name(),r.displayName()));
	    }
	}	
    }
    

    /**
     * true, if the argument should be used for test
     * TODO implement
     */
    public boolean useRuleForTest(int arg) {
	return true;
    }

    
    
    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {	
        props.setProperty(ACTIVE_RULE, "" + activeRule);
        props.setProperty(TIMEOUT, "" + this.timeout);
    }

    public static DecisionProcedureSettings getInstance() {
	if (instance == null) {
	    instance = new DecisionProcedureSettings();
	}
	
	return instance;
    }

}
