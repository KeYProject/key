// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SmtSolver;
import de.uka.ilkd.key.smt.YicesSmtSolver;
import de.uka.ilkd.key.smt.Z3Solver;
import de.uka.ilkd.key.unittest.ModelGenerator;

/** This class encapsulates the information which 
 *  decision procedure should be used.
 */
public class DecisionProcedureSettings implements Settings {
    
    /** String used in the Settings to store the active rule */
    private static final String ACTIVE_RULE  = "[DecisionProcedure]ActiveRule";
    
    private static final String TIMEOUT="[DecisionProcedure]Timeout";
    
    /** String used in the Settings to store the available rules */
    //private static final String AVAILABLE_RULES  = "[DecisionProcedure]AvailableRules";
    
    /** the list of registered SettingListener */
    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();

    /** the list of available SMTRules */
    private ArrayList<SMTRule> rules = new ArrayList<SMTRule>();
    
    /** the currently active rule */
    int activeRule = -1;
    
    int timeout = 60;
    
    private static DecisionProcedureSettings instance;
    
    /**
     * This is a singelton.
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
     * Get the names of all available active rules
     */
    public ArrayList<String> getAvailableRules() {
	ArrayList<String> toReturn = new ArrayList<String>();
	for (SMTRule r : this.rules) {
	    toReturn.add(r.displayName());
	}
	return toReturn;
    }
    
    /**
     * get the index of the currently active rule
     */
    public int getActiveRuleIndex() {
	if (this.rules.size() == 0) {
	    this.activeRule = -1;
	} else if (this.activeRule < 0 || this.activeRule >= this.rules.size()) {
	    this.activeRule = 0;
	    this.fireSettingsChanged();
	}
	return this.activeRule;
    }
    
    public SMTRule getActiveRule() {
	if (this.activeRule < 0 || this.activeRule >= this.rules.size()) {
	    return null;
	} else {
	    return this.rules.get(this.activeRule);
	}
    }
    
    /**
     * Set the active Rule
     */
    public void setActiveRule(int ar) {
	if (0 <= ar && ar < this.rules.size()) {
	    this.activeRule = ar;
	    this.fireSettingsChanged();
	} else {
	    //use 0 as default
	    this.activeRule = 0;
	    this.fireSettingsChanged();
	}
    }
    
    public void setTimeout(int t) {
	if (t > 0) {
	    this.timeout = t;
	    this.fireSettingsChanged();
	}
    }
    
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
	//Load the available Solver
	rules = new ArrayList<SMTRule>();
	rules.add(new SMTRule(new SimplifySolver()));
	rules.add(new SMTRule(new Z3Solver()));
	rules.add(new SMTRule(new YicesSmtSolver()));
		
	String ruleString = props.getProperty(ACTIVE_RULE);
	this.activeRule = -1;
	if(ruleString != null) {
	    int curr = Integer.parseInt(ruleString);
	    if (curr >= 0 && curr < rules.size()) {
		this.activeRule = curr;
	    }
	}
	
	String timeoutstring = props.getProperty(TIMEOUT);
	if (timeoutstring != null) {
	    int curr = Integer.parseInt(timeoutstring);
	    if (curr > 0) {
		this.timeout = curr;
	    }
	}
    }


    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
        props.setProperty(ACTIVE_RULE, "" + this.activeRule);
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

}
