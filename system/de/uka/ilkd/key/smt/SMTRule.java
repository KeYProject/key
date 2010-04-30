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
import java.util.HashSet;
import java.util.LinkedList;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.smt.TacletTranslationSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTProgressMonitor.SolveType;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.smt.SolverSession.InternResult;
import de.uka.ilkd.key.smt.launcher.Event;
import de.uka.ilkd.key.smt.launcher.Process;
import de.uka.ilkd.key.smt.launcher.ProcessLaunch;
import de.uka.ilkd.key.smt.launcher.ProcessLauncher;
import de.uka.ilkd.key.smt.launcher.ProcessLauncherListener;


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
 *  Use this class to apply external provers to goals. Do not directly use
 *  the solver classes.<br>
 *  The SMTRule manages the executing of the solvers. There are two ways
 *  to execute solvers:<br><br>
 *  1. start(...): Starts and monitors the solvers belonging to the rule. (Boss-Worker-Model)<br>
 *  You can decide whether the starting and monitoring (Boss) should be executed
 *  in a new thread or not.<br> Be aware of the fact that in both cases the solvers (workers)
 *  are executed in new threads.<br>
    After executing the solvers their results are collected, 
 *  which can be read by <code>getResults()</code> or can be applied to their 
 *  corresponding goals by <code>applyGoals()</code>.<br>
 *  2. run(...): Makes use of the 1.<br>
 *  If you want to run the solvers without applying the results to the corresponding 
 *  goals you can use these methods. They are practical if you want to run solvers
 *  on single goals or formulae in a sequential way: The methods do not create
 *  threads for starting and monitoring the solvers.<br>
 *  (The solvers (workers )themselves use new threads and run concurrently.)
 */
public class SMTRule  extends ProcessLauncher implements BuiltInRule{

    
    

    /**Used for consistency.*/
    public final static SMTRule EMPTY_RULE = new EmptyRule();
    /**The solvers that are used by this rule.*/
    private Collection<SMTSolver> solvers = new LinkedList<SMTSolver>();
    /**Important for applying the results to goals.*/
    private Constraint 	           userConstraint = null;
    /**The name of the rule. Important to identify rules while reading and   
     * writting the settings.*/
    private Name 	           name;
    /**
     * <code>true</code> if <code>solvers.size()>1</code>,
     *  otherwise <code>false</code> 
     */
    private final boolean 	   multiRule;
    
    private final boolean background;

    
    
    
    
    
    public enum WaitingPolicy {STOP_FIRST,WAIT_FOR_ALL};
 
  
    public void init(){
	userConstraint = null;
	super.init();
    }
    
    private SMTRule(Name name,boolean multi, boolean background ,SMTSolver ... list){
	multiRule = multi;
	this.background = background;
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
    public SMTRule(Name name, SMTSolver ... list){
	this(name,list.length>1,false,list);
	
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
            Constraint uc) {
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

    

    /** Interrupts the current execution of the solvers. */
    public void stop(){
	this.cancelMe();
    }
    
    private void prepareSolvers(LinkedList<InternResult> terms, Services services, Collection<Taclet> taclets){
	for(SMTSolver solver : getInstalledSolvers()){
	    LinkedList<InternResult> temp = new LinkedList<InternResult>();
	    for(InternResult ir : terms){
		temp.add((InternResult) ir.clone(solver));
	      
	    }
	    solver.prepareSolver(temp, services, taclets);
	    addProcess(solver);
	}
    }
    
    /**
     * Starts the rule, i.e. a new thread for the rule is created and the 
     * external prover, belonging to this rule, will be started in new threads.
     * @param goal 
     * @param constraint
     */
    public void start(Goal goal, Constraint constraint){
	start(goal, constraint, true,WaitingPolicy.WAIT_FOR_ALL);
    }
    
    public void start(Goal goal, Constraint constraint, boolean useThread){
	start(goal, constraint, useThread, WaitingPolicy.WAIT_FOR_ALL);
    }
    
    /**
     * Starts the rule. 
     * @param goal
     * @param constraint
     * @param useThread <code>true</code> if you want to start this rule in a new thread.
     */
    public void start(Goal goal, Constraint constraint, boolean useThread, WaitingPolicy applyPolicy){
	init();
	LinkedList<Goal> goals = new LinkedList<Goal>();
	goals.add(goal);
	start(goals,goal.proof(),constraint,useThread,applyPolicy);
    }
    
    /**
     * Starts the rule, i.e. a new thread for the rule is created and the 
     * external prover, belonging to this rule, will be started in new threads.
     * @param goals
     * @param proof proof the goals belonging to.
     * @param constraint
     */
    public void start(Collection<Goal> goals, Proof proof, Constraint constraint){
	start(goals, proof, constraint,true,WaitingPolicy.WAIT_FOR_ALL);
    }
    
    
    public void start(Collection<Goal> goals, Proof proof, Constraint constraint,
	    boolean useThread){
	start(goals,proof,constraint,useThread, WaitingPolicy.WAIT_FOR_ALL);
    }
    
    public void start(Collection<Goal> goals, Proof proof, Constraint constraint,
	    boolean useThread, WaitingPolicy applyPolicy){
	init();

	LinkedList<InternResult> terms = new LinkedList<InternResult>();
	TacletIndex index=null;
	for(Goal goal : goals){
	    Term term = goalToTerm(goal);
	    terms.add(new InternResult(term,goal));
	    index = goal.indexOfTaclets();
	}
	
	startThread(terms,constraint,useThread,index,proof.getServices(), applyPolicy);

	
    }
    
    private Term goalToTerm(Goal goal){
	Sequent s = goal.sequent();
	
	ImmutableList<Term> ante = ImmutableSLList.nil();
	
	ante = ante.append(TermBuilder.DF.tt());
	for(ConstrainedFormula f : s.antecedent()){
	    ante = ante.append(f.formula());
	}
	
	ImmutableList<Term> succ = ImmutableSLList.nil();
	succ = succ.append(TermBuilder.DF.ff());
	for(ConstrainedFormula f : s.succedent()){
	    succ = succ.append(f.formula());
	}
	
	
	return TermBuilder.DF.imp(TermBuilder.DF.and(ante), TermBuilder.DF.or(succ));
	
    }
    
    public void start(Term term, Services services, Constraint constraint, boolean useThread,
	    TacletIndex index){
	LinkedList<Term> list = new LinkedList<Term>();
	list.add(term);
	start(list, services, constraint, useThread, index);
    }
    
    public void start(Collection<Term> terms, Services services, Constraint constraint, boolean useThread,
	    TacletIndex index){
	LinkedList<InternResult> internTerms = new LinkedList<InternResult>();
	for(Term term : terms){
	    internTerms.add(new InternResult(term, null));
	}
	startThread(internTerms,constraint,useThread,index,services,WaitingPolicy.WAIT_FOR_ALL);
    }
    
    

    
    /**
     * DO NOT USE THIS METHOD IF THERE IS ANOTHER WAY TO SOLVE YOUR PROBLEM.
     * This method was introduced to guarantee that SimplifyModelGenerator
     * works further on.
     * Use the method only with SMTRules, that consists of only one solver.
     * @param formula
     * @param services
     * @param constraint
     * @param useThread
     */
    private void start(String formula, Services services, Constraint constraint, boolean useThread){
	LinkedList<InternResult> list = new LinkedList<InternResult>();
	list.add(new InternResult(formula));
	startThread(list,constraint,useThread,null,services,WaitingPolicy.WAIT_FOR_ALL);
    }
    

    
    private void startThread(LinkedList<InternResult> terms,Constraint constraint, boolean useThread, TacletIndex index,
	      Services services, WaitingPolicy applyPolicy){
	init();

	this.setFirstClosePolicy(applyPolicy == WaitingPolicy.STOP_FIRST);
	userConstraint = constraint;
	Collection<Taclet>  taclets = TacletTranslationSettings.getInstance().initTaclets(index);
	
	prepareSolvers(terms,services,taclets);	
	if(useThread){
		Thread thread = new Thread(this,displayName());
		thread.setDaemon(true);
		thread.start();
	}else{
	    this.run();
    
	}

    }
    
    /**
     * Use this method if you only want to run the solvers that belong to the rule without
     * applying the results to goals. This method does not start an extra thread for starting
     * the solvers. 
     * On account of this the method returns not until the solvers have finished their jobs. 
     * @param term the term to be solved
     * @param services 
     * @param constraint
     * @param tacletIndex
     */
    public SMTSolverResult run(Term term , Services services, Constraint constraint,
	    TacletIndex tacletIndex){
	start(term,services,constraint,false, tacletIndex);
	return this.getResults().getFirst();
    }
    
    /**
     * Use this method if you only want to run the solvers that belong to the rule without
     * applying the results to the goals. This method does not start an extra thread for starting
     * the solvers. 
     * On account of this the method returns not until the solvers have finished their jobs. 
     * @param goal the goal to be proofed
     * @param services 
     * @param constraint
     */
    public SMTSolverResult run(Goal goal, Services services, Constraint constraint){
	start(goal,constraint,false,WaitingPolicy.WAIT_FOR_ALL);
	return this.getResults().getFirst();
    }
    

    /**
     * Use this method if you only want to run the solvers that belong to the rule without
     * applying the results to goals. This method does not start an extra thread for starting
     * the solvers. 
     * On account of this the method returns not until the solvers have finished their jobs. 
     * IMPORTANT: Use this method only if it consists of only one prover.
     * @param formula the formula to be proofed. The formula must use the format of the solver
     * that belongs to this rule. 
     * @param services 
     * @param constraint
     * @return the result of the executed proofer. If the rule consists of multiple provers
     * the method returns <code>null</code>.
     */
    public SMTSolverResult run(String formula, Services services, Constraint constraint){
	if(multiRule){
	    return null;
	}
	start(formula,services,constraint,false);
	return this.getResults().getFirst();
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
	    if((!solver.isInstalled(true) || !solver.useForMultipleRule()) && multiRule){
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
     * Applies the results to the proved goals.
     * If you use an own thread for this rule (see <code>start(...)<code>), you
     * must call this method after executing the external provers.
     */
    public void applyResults() {

	LinkedList<SolverSession.InternResult> result = new LinkedList<SolverSession.InternResult>();
	for (SMTSolver solver : getInstalledSolvers()) {
	    // if( !solver.running()){
	    AbstractSMTSolver s = (AbstractSMTSolver) solver;

	    result.addAll(s.getSession().getResults());
	    // }

	}
	if (result.size() == 0) {
	    return;
	}

	for (final SolverSession.InternResult res : result) {
	    final BuiltInRuleApp birApp = new BuiltInRuleAppSMT(this, null,
		    userConstraint, res.getResult());
	    Goal goal = res.getGoal();

	    if (goal != null) {

		res.getGoal().node().addSMTandFPData(res.getResult());
		if (!goal.proof().closed() &&goal.proof().openGoals().contains(goal)) {

		    if (res.getResult().isValid() == ThreeValuedTruth.TRUE) {

			goal.apply(birApp);

		    }
		}

	
	    }

	}

    }
    
    
    /**
     * @return returns the results of the last execution. <br>
     * If the rule consists of multiple provers: The method does not merge the results in a semantic way,
     * but add them all to the returned list.
     */
    public LinkedList<SMTSolverResult> getResults(){
	HashSet<SolverSession.InternResult> result = new HashSet<SolverSession.InternResult>();
	
	for(SMTSolver solver : getInstalledSolvers()){
	    AbstractSMTSolver s = (AbstractSMTSolver) solver;

	    result.addAll(s.getSession().getResults());
	  
	}
	LinkedList<SMTSolverResult> toReturn = new LinkedList<SMTSolverResult>();
	
	for(SolverSession.InternResult res  : result ){
	    toReturn.add(res.getResult());
	}
	return toReturn;
	
    }
    
    public String toString(){
	return displayName();
    }
    

    private long getCurrentProgress(long time, long maxTime){
	   return (long)  
	   ((double)time/maxTime*SMTProgressMonitor.MAX_TIME);  
    }
    
    private double cut(double time, int digits){
	long temp = (long) (time*(double)Math.pow(10, digits));
	return ((double)temp)/Math.pow(10, digits);
    }
    
    private void showTimeStatus(SMTProgressMonitor mon, long time, long maxTime, boolean finished){
	
	double t = cut(((double)time)/1000,1);
	
	String s = (finished ? "Stopped after " : "") +t+" sec.";
	if(finished){
	    mon.setFinished();
	}
	mon.setTimeProgress(s, getCurrentProgress(time, maxTime));
    }
    
 

    @Override
    protected void publish(Event e) {

	if(e.getType().equals(Event.Type.WORK_DONE)){
	    for(ProcessLauncherListener l : listener){
		l.workDone();
	    }
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
	
	long runningTime =  launch.runningTime(
		     System.currentTimeMillis());
	 
	 
	 switch(e.getType()){
	 case PROCESS_START:
	     monitor.setGoalMaximum(process.getMaxCycle());
	     break;
	 case PROCESS_STATUS:
	     showTimeStatus(monitor,runningTime ,launcher.getMaxTime(), false);
	     break;

	 case PROCESS_CYCLE_FINISHED:
	       AbstractSMTSolver solver = (AbstractSMTSolver)process;
	        SMTSolverResult result = (SMTSolverResult)e.getUserObject();
	
	        if(result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE){
	
	            monitor.setGoalProgress(solver.getSession().currentTerm().getGoal(), SolveType.SOLVABLE);
	        }
	        if(result.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE){
	            monitor.setGoalProgress(solver.getSession().currentTerm().getGoal(), SolveType.UNSOLVABLE);  
	        }
	     break;
	     
	 case PROCESS_EXCEPTION:
	     if(background){
		 throw new RuntimeException(e.getException());
	     }else{
	     monitor.exceptionOccurred("Error while executing " + process.getTitle()+"."
		     ,e.getException());
	     }
	     break;
	 
	 
	 case INTERRUP_PROCESS:
	      showTimeStatus(monitor,launcher.getMaxTime(),launcher.getMaxTime(), true);
	      
	      break;
	case PROCESS_FINISHED:
	     showTimeStatus(monitor,launch.usedTime() ,launcher.getMaxTime(), true);
	     break;

	 
	     
	 default:
	     break;
	 }
	 
	
    }
    
   

}

/**
 * The empty representation of the the SMTRule.
 */
class EmptyRule extends SMTRule{
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
	return "No prover available";

    }

    
  
    
 
    
    public void applyResults(){
    }
    




    @Override
    protected void publish(Event e) {
    }
}
