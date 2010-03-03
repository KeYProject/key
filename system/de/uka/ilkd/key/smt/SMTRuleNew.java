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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
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

class BuiltInRuleAppSMT extends BuiltInRuleApp{
    final SMTSolverResult result;
    public BuiltInRuleAppSMT(BuiltInRule builtInRule, PosInOccurrence pio,
            Constraint userConstraint, SMTSolverResult result) {
	super(builtInRule, pio, userConstraint);
	this.result = result;
    }
    public SMTSolverResult getResult(){return result;}
    
}


public class SMTRuleNew  extends ProcessLauncher implements BuiltInRule{

    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    private Constraint 	           userConstraint = null;
    private Proof		   proof;
 
    public void init(){
	userConstraint = null;
	proof = null;
	super.init();
    }
    
    
    public SMTRuleNew(SMTSolver ... list){
	for(SMTSolver solver : list){
	   solvers.add(solver);   
	}
    }
    

    public boolean isApplicable(Goal goal, PosInOccurrence pio,
            Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }

    public Collection<SMTSolver> getInstalledSolvers(){
	Collection<SMTSolver> installed = new LinkedList<SMTSolver>();
	for(SMTSolver solver : solvers){
	    if(solver.isInstalled(false)){
		installed.add(solver);
	    }
	}
	return installed;
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
    
    public void stop(){
	this.cancelMe();
    }
    
    private void prepareSolvers(Collection<Goal> goals, Services services){
	for(SMTSolver solver : getInstalledSolvers()){
	    addSolver(solver,goals,services);
	}
    }
    
    public void start(Goal goal, Constraint constraint){
	init();
	LinkedList<Goal> goals = new LinkedList<Goal>();
	goals.add(goal);
	proof = goal.proof();
	startThread(goals,constraint);
    }
    
    public void start(Proof proof, Constraint constraint){
	init();
	LinkedList<Goal> goals = new LinkedList<Goal>();
	this.proof = proof;
	for (Goal goal : proof.openGoals()) {
	     goals.add(goal);
	}
	
	
	startThread(goals,constraint);
    }
    
    private void startThread(Collection<Goal> goals,Constraint constraint){
	userConstraint = constraint;
        proof.env().registerRule(this,
                de.uka.ilkd.key.proof.mgt.AxiomJustification.INSTANCE);
	prepareSolvers(goals,proof.getServices());	
	Thread thread = new Thread(this,displayName());
	thread.start();
    }
    
    

    public String displayName() {
	String s = "NEW: ";
	for(SMTSolver solver : getInstalledSolvers()){
	    s += solver.name()+" ";
	}
	return s;
    }

    
    public Name name() {
	
	return new Name(displayName());
    }
    
    public String getTitle(){
	return  displayName();
    }
    
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
    




    @Override
    protected void publish(Event e) {
	// System.out.println(e.getType().toString());
	if(e.getType().equals(Event.Type.WORK_DONE)){
	    
	    return;
	}
	
	
	SMTProgressMonitor monitor = null;
	ProcessLaunch      launch  = e.getLaunch();
	ProcessLauncher    launcher = e.getLauncher();
	if(launch == null){
	     System.out.println("launch==null");
	     return;
	}
	
	Process            process = launch.getProcess(); 
	if(process.getMonitors().isEmpty()){
	    System.out.println("no monitor: " + launch.getProcess().getTitle()+ " " + e.getType().toString()); 
	    return ;
	}
	monitor = process.getMonitors().iterator().next();
	
	
	 
	 
	 switch(e.getType()){
	 case PROCESS_START:
	     monitor.setMaximum(process.getMaxCycle());
	     monitor.setProgress(0);
	     break;
	 case PROCESS_STATUS:
	     monitor.setTimeProgress((int)((double)launch.runningTime(System.currentTimeMillis())/launcher.getMaxTime()*1000));    
	     break;
	 case INTERRUP_PROCESS:
	     monitor.setTimeProgress(1000);
	     break;
	 case PROCESS_CYCLE_FINISHED:
	       AbstractSMTSolver solver = (AbstractSMTSolver)process;
	        SMTSolverResult result = (SMTSolverResult)e.getUserObject();
	      /*  BuiltInRuleApp birApp = new BuiltInRuleAppSMT(this, null, 
	                userConstraint,result); 
	        solver.getSession().currentGoal().apply(birApp);
	     */   
	
	        System.out.println("Result " + process.getTitle()+": "+ result.toString());
	        if(result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE){
	            monitor.setGoalProgress(solver.getSession().currentGoal(), SolveType.SOLVABLE);
	        }
	     break;
	     
	     
	     
	 default:
	     break;
	 }
	 
	
    }

  
    

 
    

}
