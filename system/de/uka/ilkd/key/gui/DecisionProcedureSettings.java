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
import de.uka.ilkd.key.smt.AbstractSMTSolver;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTRuleMulti;
import de.uka.ilkd.key.smt.SMTRuleNew;
import de.uka.ilkd.key.smt.SMTSolver;
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
    
    private static final String SAVEFILE="[DecisionProcedure]savefile";
    
    private static final String SHOW_SMT_RES_DIA="[DecisionProcedure]showSMTResDialog";
    
    private static final String MULTIPLEPROVERS="[DecisionProcedure]multprovers";

    
    /**@see {@link de.uka.ilkd.key.smt.SmtLibTranslatorWeaker} */
    private static final String WEAKENSMTTRANSLATION = "[DecisionProcedure]WeakenSMTTranslation";

    /** the list of registered SettingListener */
    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();
    

    
    private LinkedList<SMTRuleNew> smtRules = new LinkedList<SMTRuleNew>();
   
    
    
    
    private static Collection<AbstractSMTSolver>  solvers = new LinkedList<AbstractSMTSolver>();
    
    /** the currently active rule */    
    private SMTRuleNew activeSMTRule = SMTRuleNew.EMPTY_RULE;
    
    /** the value of the timeout in tenth of seconds.*/
    private int timeout = 600;
    
    private static DecisionProcedureSettings instance;
    
    private static String EXECSTR = "[DecisionProcedure]Exec";
    /** mapping of rule name (key) to execution string (value) */
    private HashMap<String, String> execCommands = new HashMap<String, String>();
    
    /** the string separating different solver-command values. */
    private static final String execSeperator1 = ":"; 
    /** The String separating solvernames from commands in the settingsfile */
    private static final String execSeperator2 = "="; 
    
    /** the string separating different solvers
      */
    private static final String multSeparator1 = ":";
    
    /**the string separating solvernames from the value */
    private static final String multSeparator2 = "=";
    
    
    private String multProversSettings=null;


    
    
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
    public SMTRuleNew findRuleByName(String name){
	
	for(SMTRuleNew rule : getSMTRules()){
	    if(rule.name().toString().equals(name)){
		return rule;
	    }
	}
	return SMTRuleNew.EMPTY_RULE;
    }
    
    
    public AbstractSMTSolver findSolverByName(String name){
	for(AbstractSMTSolver solver : getSolvers()){
		    if(solver.name().equals(name)){
			return solver;
		    }
		} 
	

	return null;
    }


    
    
    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new GUIEvent(this));
        }
    }
    

    
    public SMTRuleNew getActiveSMTRule(){
	return activeSMTRule;
    }

    
    private void setSolversAndRules(){
	
	AbstractSMTSolver z3 = new Z3Solver();
	AbstractSMTSolver simplify = new SimplifySolver();
	AbstractSMTSolver yices = new YicesSolver();
	AbstractSMTSolver cvc3 = new CVC3Solver();

	solvers.add(z3);
	solvers.add(simplify);
	solvers.add(yices);
	solvers.add(cvc3);
	smtRules.add(new SMTRuleNew(new Name("Z3_PROVER"),z3));
	smtRules.add(new SMTRuleNew(new Name("YICES_PROVER"),yices));
	smtRules.add(new SMTRuleNew(new Name("SIMPLIFY_PROVER"),simplify));
	smtRules.add(new SMTRuleNew(new Name("CVC3_PROVER"),cvc3));
	smtRules.add(new SMTRuleNew(new Name("MULTIPLE_PROVERS"),z3,simplify,yices,cvc3));
	
	//solvers = s;
	
    }
    
    public final Collection<AbstractSMTSolver> getSolvers(){
	
	return solvers;
    }
    
    
    public Collection<SMTRuleNew> getSMTRules(){

	return smtRules;
    }
    

    /**
     * Returns a list of all installed rules, sorted alphabetically by rule name.
     */
    public Collection<SMTRuleNew> getInstalledRules(){
	Collection<SMTRuleNew> toReturn = new LinkedList<SMTRuleNew>();
	
	for(SMTRuleNew rule : getSMTRules()){
	    if(rule.getInstalledSolvers().size() > 0){
		toReturn.add(rule);
	    }
	}
	
	return toReturn;
    }
    
    
    
    /**
     * returns the timeout specifying the maximal amount of time an external prover
     * is run
     * @return the timeout in tenth of seconds
     */
    public int getTimeout() {
	return this.timeout;
    }
    

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	

	
	
	String timeoutstring = props.getProperty(TIMEOUT);
	if (timeoutstring != null) {
	    int curr = Integer.parseInt(timeoutstring);
	    if (curr > 0) {
		this.timeout = curr;
	    }
	}
	
	this.readExecutionString(props);
	
	multProversSettings = props.getProperty(MULTIPLEPROVERS);
	readMultProversString();
	
	
	String sf = props.getProperty(SAVEFILE);
        this.saveFile = !(sf == null) && sf.equals("true");
	
        String sd = props.getProperty(SHOW_SMT_RES_DIA);
        this.showSMTResDialog = !(sd == null) && sd.equals("true");
    
    	String wt = props.getProperty(WEAKENSMTTRANSLATION);
    	this.weakenSMTTranslation = !(wt == null) && wt.equals("true");
    	
    	
    	// Read the active rule at the end of the method to guarantee
    	// that the execution commands have been read yet.
	String ruleString = props.getProperty(ACTIVE_RULE);

	this.activeSMTRule = findRuleByName(ruleString);
	// Use only the rule if the corresponding solvers 
	// are installed.
	if(!activeSMTRule.isUsable()){
	    this.activeSMTRule = SMTRuleNew.EMPTY_RULE;
	}

    }
    

    
    /**
     * read the execution strings from the properties file
     * @param props
     */
    private void readExecutionString(Properties props) {
	String allCommands = props.getProperty(EXECSTR);
	//all value pairs are stored separated by a |
	if (allCommands != null) {
	    String[] valuepairs = allCommands.split(execSeperator1);
	    for (String s : valuepairs) {
		String[] vals = s.split(execSeperator2);
		if (vals.length == 2) {
		    AbstractSMTSolver solver = findSolverByName(vals[0]);
		    if(solver != null){
			setExecutionCommand(solver,vals[1]);
			solver.isInstalled(true);
		    }
		}
	    }
	}
    }
    
    
    /**
     * read the multiple provers strings from the properties file, stored in multProversSettings
     */
    private void readMultProversString()
    {
	
	
	if(multProversSettings != null){
	    String[] valuepairs = multProversSettings.split(multSeparator1);
	    for(String s : valuepairs){
		String[] vals = s.split(multSeparator2);
		if(vals.length == 2){
		    AbstractSMTSolver solver = findSolverByName(vals[0]);
		    if(solver != null){
			solver.useForMultipleRule(vals[1].equals("true"));
		    }
			
			
			
		   
		}
	    }
	}
    }
    
    /**
     * write the Execution Commands to the file
     * @param prop
     */
    private void writeExecutionString(Properties prop) {
	String toStore = "";
	for (AbstractSMTSolver solver : getSolvers()) {
	     
	     String comm = solver.getExecutionCommand();
	    	if (comm == null) {
			comm = "";
	    	}
	    	toStore = toStore + solver.name() + execSeperator2 + comm + execSeperator1;
	    }
	
	//remove the las two || again
	if (toStore.length() >= execSeperator1.length()){
	    //if the program comes here, a the end ad extra || was added.
	    toStore = toStore.substring(0, toStore.length()-execSeperator1.length());
	}
	prop.setProperty(EXECSTR, toStore);
    }
    
    /**
     * Write the values, that specify whether a prover is used for the rule 'multiple provers'. 
     */
    private void writeMultipleProversString(Properties prop) {
	String toStore = "";
	
	for(AbstractSMTSolver solver : solvers){
	    String value = solver.useForMultipleRule()? "true" : "false";
	    toStore = toStore + solver.name() + multSeparator2 + value + multSeparator1; 
	}


	if (toStore.length() >= multSeparator1.length()){
	    toStore = toStore.substring(0, toStore.length()-multSeparator1.length());
	}
	prop.setProperty(MULTIPLEPROVERS, toStore);
    }
    

    
    /**
     * Set a execution command for a certain solver.
     * @param s the solver, which uses this command.
     * @param command the command to use
     */
    public void setExecutionCommand(AbstractSMTSolver s, String command) {
	
	s.setExecutionCommand(command);
	
    }
    
    /**
     * get the execution command for a certain rule.
     * @param r the rule
     * @return the execution command
     */
    public String getExecutionCommand(AbstractSMTSolver solver) {
	return solver.getExecutionCommand();
    }
    



    


    
    public boolean getMultipleUse(AbstractSMTSolver solver){
	return solver.useForMultipleRule();
    }
    
    
   /* public boolean getMultipleUse(RuleDescriptor rd)  {
	SMTRule rule = descriptorToRule.get(rd);
	SMTSolver s = rule.getSolver();
	return this.ruleMultipleProvers.SMTSolverIsUsed(s);
    }*/
    
   /* public void setMultipleUse(RuleDescriptor rd, boolean multipleuse, boolean fire) {
	SMTRule rule = descriptorToRule.get(rd);
	SMTSolver s = rule.getSolver();
	ruleMultipleProvers.useSMTSolver(s, multipleuse);
	if(fire)
	fireSettingsChanged();
    }*/
    
    
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
    public void setActiveSMTRule(SMTRuleNew rule){
	if(activeSMTRule != rule){
	    if(rule == null){
		activeSMTRule = SMTRuleNew.EMPTY_RULE;
	    }else{
		this.activeSMTRule = rule;
	    }
	 
	    fireSettingsChanged();
	}
	

    }


    /**
     * sets the timeout until an external prover is terminated
     * @param t the timeout in tenth of seconds
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
	//Load the available SMTRules...	
	/*for (Rule r : profile.
		getStandardRules().getStandardBuiltInRules()) {
	    if(r instanceof SMTRuleNew){
		this.smtRules.add((SMTRuleNew)r);
	    }
	}*/
	
    }
    
    private boolean saveFile = false;


    
    public void setSaveFile(boolean sf) {
	if (sf != this.saveFile) {
	    this.saveFile = sf;
	    this.fireSettingsChanged();
	}
    }
    
    /**
     * returns true, if a created problem file should be saved.
     * @return
     */
    public boolean getSaveFile() {
	return this.saveFile;
    }
    
    private boolean showSMTResDialog = false;
    
    /**@see {@link de.uka.ilkd.key.smt.SmtLibTranslatorWeaker} */
    public boolean weakenSMTTranslation = false;
    
    public void setSMTResDialog(boolean b){
	if(b!=this.showSMTResDialog){
	    this.showSMTResDialog = b;
	    this.fireSettingsChanged();
	}
    }
    
    public boolean getShowSMTResDialog(){
	return this.showSMTResDialog;
    }
    
    /**
     * true, if the argument should be used for test
     * TODO implement?
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
        props.setProperty(ACTIVE_RULE, "" + activeSMTRule.name());
        props.setProperty(TIMEOUT, "" + this.timeout);
      
        if (this.saveFile)
            props.setProperty(SAVEFILE, "true");
        else {
            props.setProperty(SAVEFILE, "false");
        }
        if (this.showSMTResDialog)
            props.setProperty(SHOW_SMT_RES_DIA, "true");
        else {
            props.setProperty(SHOW_SMT_RES_DIA, "false");
        }

        if (this.weakenSMTTranslation)
            props.setProperty(WEAKENSMTTRANSLATION, "true");
        else {
            props.setProperty(WEAKENSMTTRANSLATION, "false");
        }

       
        this.writeExecutionString(props);
        this.writeMultipleProversString(props);
    }

    public static DecisionProcedureSettings getInstance() {
	if (instance == null) {
	    instance = new DecisionProcedureSettings();
	    instance.setSolversAndRules();
	}
	
	return instance;
    }





 

}
