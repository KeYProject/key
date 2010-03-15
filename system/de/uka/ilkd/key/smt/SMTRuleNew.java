// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import com.sun.org.apache.bcel.internal.generic.GETSTATIC;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.DecisionProcedureSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.smt.SMTProgressMonitor.SolveType;
import de.uka.ilkd.key.smt.launcher.Event;
import de.uka.ilkd.key.smt.launcher.Process;
import de.uka.ilkd.key.smt.launcher.ProcessLaunch;
import de.uka.ilkd.key.smt.launcher.ProcessLauncher;
import de.uka.ilkd.key.util.ProgressMonitor;


/**
 * Applies the result of external provers to goals.  
 *
 */
class BuiltInRuleAppSMT extends BuiltInRuleApp{
    final SMTSolverResult result;
    public BuiltInRuleAppSMT(BuiltInRule builtInRule, PosInOccurrence pio,
            Constraint userConstraint, SMTSolverResult result) {
	super(builtInRule, pio, userConstraint);
	this.result = result;
    }
    public SMTSolverResult getResult(){return result;}
    
}



/**
 *  Use this class to apply external provers to goals. Do not use directly
 *  the solver classes.
 */
public class SMTRuleNew  extends ProcessLauncher implements BuiltInRule{

    
    

    /**Used for consistency.*/
    public final static SMTRuleNew EMPTY_RULE = new EmptyRule();
    /**The solvers that are used by this rule.*/
    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    /**Important for applying the results to goals.*/
    private Constraint 	           userConstraint = null;
    /**The current proof*/
    private Proof		   proof;
    /**The name of the rule. Important to identify rules while reading and 
     * writting the settings.*/
    private Name 	           name;
    /**
     * <code>true</code> if <code>solvers.size()>1</code>,
     *  otherwise <code>false</code>
     */
    private final boolean 	   multiRule;
    
    
 
  
    public void init(){
	userConstraint = null;
	proof = null;
	super.init();
    }
    
    private SMTRuleNew(Name name,boolean multi ,SMTSolver ... list){
	multiRule = multi;
	
	for(SMTSolver solver : list){
		   solvers.add(solver);   
	}
	this.name = name;
    
    }
    
    /**
     * @param name The name of the SMTRule.
     * @param list the list of solvers, that should be used by 
     * by the rule.
     */
    public SMTRuleNew(Name name, SMTSolver ... list){
	this(name,list.length>1,list);
	
    }
    
    /**
     * @return <code>true</code> iff the rule contains enough 
     * installed solvers, i.e. <br>
     * 1. if the rule consists of one solver,
     * this solver must be installed.<br>
     * 2. if the rule consists of multiple solvers,
     * at least two solvers must be installed.
     */
    public boolean isUsable(){
	return getInstalledSolvers().size() > 0;
    }
    
    /**
     * @return a collection of all installed solvers. <br>
     * 1. If there is not any solver installed the method returns an empty collection. 
     * 2. If the rule consists of multiple solvers at least two solvers must be installed.
     */    
    public Collection<SMTSolver> getInstalledSolvers(){
	Collection<SMTSolver> installed = new LinkedList<SMTSolver>();
	for(SMTSolver solver : solvers){
	    if(solver.isInstalled(false) && 
		    (((((AbstractSMTSolver)solver).useForMultipleRule() && multiRule)) || !multiRule)){
		
		installed.add(solver);
	    }
	}
	if(multiRule && installed.size() == 1){
	    installed.clear();
	}
	return installed;
    }
    

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
            Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }



    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {
	
	assert ruleApp instanceof BuiltInRuleAppSMT;
	
	SMTSolverResult result = ((BuiltInRuleAppSMT)ruleApp).getResult();
	
	if (result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) {
	    return ImmutableSLList.<Goal>nil();
	} else {
	    return null;
	}
    }

    
    private void addSolver(SMTSolver solver, Collection<Goal> goals, Services services){
	solver.prepareSolver(goals, services);

	addProcess(solver);	
    }
    
    /** Interrupts the current execution of the solvers. */
    public void stop(){
	this.cancelMe();
    }
    
    private void prepareSolvers(Collection<Goal> goals, Services services){
	for(SMTSolver solver : getInstalledSolvers()){
	    addSolver(solver,goals,services);
	}
    }
    
    /**
     * Starts the rule, i.e. a new thread for the rule is created and the 
     * external prover, belonging to this rule, will be started.
     * @param goal 
     * @param constraint
     */
    public void start(Goal goal, Constraint constraint){
	init();
	LinkedList<Goal> goals = new LinkedList<Goal>();
	goals.add(goal);
	proof = goal.proof();
	startThread(goals,constraint);
    }
    
    /**
     * Starts the rule, i.e. a new thread for the rule is created and the 
     * external prover, belonging to this rule, will be started.
     * @param goals
     * @param proof proof the goals belonging to.
     * @param constraint
     */
    public void start(Collection<Goal> goals, Proof proof, Constraint constraint){
	init();
	this.proof = proof;
	startThread(goals,constraint);
    }
    

    
    private void startThread(Collection<Goal> goals,Constraint constraint){
	this.setMaxTime(DecisionProcedureSettings.getInstance().getTimeout()*100);
	userConstraint = constraint;
        proof.env().registerRule(this,
                de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);
	prepareSolvers(goals,proof.getServices());	
	Thread thread = new Thread(this,displayName());
	thread.setDaemon(true);
	thread.start();
    }
    
    
    /**
     * Returns the title of the rule used by the GUI. 
     */
    public String displayName() {
	String s = "";
	int i=0; 
	
	if(multiRule && !isUsable()){
	    return "multiple provers: disabled";
	}
	
	for(SMTSolver solver : solvers){
	    if(!solver.isInstalled(false) && multiRule){
		i++;
		continue;
	    }
	  
	    if(multiRule){
	
		    
		 i++;
		 if(i > 1){
		     s += ", ";
		    }
	    }
	    
	    s += solver.name();

	}
	return s;
    }

    public Name name() {
	
	return name;
    }
    
    /**
     * @return returns the the title of the rule. Used by <code>ProgressDialog</code>.
     */
    public String getTitle(){
	return  displayName();
    }
    
    
    /**
     * After executing the external provers you must call this method to apply the results
     * to the proved goals.
     */
    public void applyResults(){
	
	HashSet<SolverSession.InternResult> result = new HashSet<SolverSession.InternResult>();
	
	for(SMTSolver solver : getInstalledSolvers()){
	    AbstractSMTSolver s = (AbstractSMTSolver) solver;

	    result.addAll(s.getSession().getResults());
	}
	for(SolverSession.InternResult res  : result ){
	    BuiltInRuleApp birApp = new BuiltInRuleAppSMT(this, null, 
	                userConstraint,res.result); 
	    res.goal.apply(birApp);
	}
    }
    
    public String toString(){
	return displayName();
    }
    




    @Override
    protected void publish(Event e) {

	if(e.getType().equals(Event.Type.WORK_DONE)){
	    
	    return;
	}
	
	
	SMTProgressMonitor monitor = null;
	ProcessLaunch      launch  = e.getLaunch();
	ProcessLauncher    launcher = e.getLauncher();
	if(launch == null){
	     return;
	}
	
	Process            process = launch.getProcess(); 
	if(process.getMonitors().isEmpty()){
	    return ;
	}
	monitor = process.getMonitors().iterator().next();
	
	
	 
	 
	 switch(e.getType()){
	 case PROCESS_START:
	     monitor.setMaximum(process.getMaxCycle());
	     monitor.setProgress(0);
	     break;
	 case PROCESS_STATUS:
	     monitor.setTimeProgress((int)((double)launch.runningTime(
		     System.currentTimeMillis())/launcher.getMaxTime()*SMTProgressMonitor.MAX_TIME));    
	     break;

	 case PROCESS_CYCLE_FINISHED:
	       AbstractSMTSolver solver = (AbstractSMTSolver)process;
	        SMTSolverResult result = (SMTSolverResult)e.getUserObject();
	
	        if(result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE){
	            monitor.setGoalProgress(solver.getSession().currentGoal(), SolveType.SOLVABLE);
	        }
	     break;
	     
	 case PROCESS_EXCEPTION:
	     monitor.exceptionOccurred("Error while executing " + process.getTitle()+"."
		     ,e.getException());
	     break;
	 
	 
	 case INTERRUP_PROCESS:
	     monitor.setTimeProgress(SMTProgressMonitor.MAX_TIME);
	    //$FALL-THROUGH$
	case PROCESS_FINISHED:
	     monitor.setSolverFinished(launch.usedTime());
	     break;
	     
	 
	     
	 default:
	     break;
	 }
	 
	
    }
    
   

}

/**
 * The empty representation of the the SMTRule.
 */
class EmptyRule extends SMTRuleNew{
    public void init(){
    }
    
    
    public EmptyRule(){
	super(new Name("EMPTY_RULE"));
    }
    

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
            Constraint userConstraint) {
	return false;
    }

    public Collection<SMTSolver> getInstalledSolvers(){
	Collection<SMTSolver> installed = new LinkedList<SMTSolver>();
	return installed;
    }

    public ImmutableList<Goal> apply(Goal goal, Services services,
            RuleApp ruleApp) {
	return null;
    }

  
    
    public void start(Goal goal, Constraint constraint){
    }
    
    public void start(Proof proof, Constraint constraint){
    }
    

    

    public String displayName() {
	return "N/A";

    }

    
  
    
 
    
    public void applyResults(){
    }
    




    @Override
    protected void publish(Event e) {
    }
}
