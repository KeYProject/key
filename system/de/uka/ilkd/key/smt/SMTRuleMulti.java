package de.uka.ilkd.key.smt;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Timer;
import java.util.WeakHashMap;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;
import de.uka.ilkd.key.util.ProgressMonitor;


/** Wrapper of the class SMTSolver, to associate processes and results with the given solver.
  */
class SolverWrapper
{
 
  /**The process associated with the solver */
  private Process Proc = null;
  /**The solver itself, can be changed only by the constructor */
  private SMTSolver  Solver;
  /**The result associated with the solver*/
  private SMTSolverResult Result = SMTSolverResult.NO_IDEA;
  /**If true, the solver is used for proving*/
  private boolean 	   UsedForProving=true;
  /**Stores the result of the external prover*/
  private String Text="";
  /**Stores the error message of the external prover*/
  private String ErrorText="";
  /**The exitValue of the external prover*/
  private int    exitValue =0; 
  /**When the external prover has finished <code>Finished</code> should be set by calling <code>setFinished(true)</code>*/  
  private boolean        Finished=false;
  
  /**For user feedback we want to know on which node (goal) a decision procedure was working on when it finishes.
   * {@see de.uka.ilkd.key.gui.DecisionProcedureResultsDialog} */
  private Goal goal=null; 

  /**Remark: Whether the variable <code>Finished</code> is set to <code>true</code> depends on whether the user of this class has called <code>setFinished(true)</code>.<br>
   * There isn't any mechanism inside this class to check the status of the external prover.
   * 
   * @return true, if the variable <code>Finished</code> is set to true.
   */
  public boolean hasFinished() {
    return Finished;
  }


  /**
   * If the external prover has finished, call this method, to interpret the result.
   * @param finished
   * @throws IOException
   */
  public void setFinished(boolean finished) throws IOException {
      
    Finished = finished;
    
    if(Finished){
	
	    InputStream in = Proc.getInputStream();
	    Text = AbstractSMTSolver.read(in);
	    in.close();
		
	    in = Proc.getErrorStream();
	    ErrorText = AbstractSMTSolver.read(in);
	    in.close();
	    exitValue = Proc.exitValue();
	    
	    Result = interpretAnswer();
	    //The following causes a notification of the DecisionProcedureResultsDialog
	    goal.node().addSMTData(Result);
    }
    else {
	Text = "";
	ErrorText = "";
	exitValue =0;

    }
    
  }




/**
   * 
   * @param solver The solver which should be wrapped.
   */
  public SolverWrapper(SMTSolver solver) {
    super();
    Solver = solver;
  }

  
  public SMTSolverResult getResult() {
    return Result;
  }

  public void setResult(SMTSolverResult result) {
    Result = result;
  }

  /** 
   * @return true, if the solver is used for proving. 
   */
  public boolean isUsedForProving() {
    return UsedForProving;
  }

  public void setUsedForProving(boolean usedForProving) {
    UsedForProving = usedForProving;
  }

  /** 
   * @return Returns the process associated with the solver.
   */
  public Process getProc() {
    return Proc;
  }

  /**
   * @return Returns the solver associated with this wrapper class.
   */
  public SMTSolver getSolver() {
    return Solver;
  }

  
  public void run(Goal goal, Services services) throws IOException, IllegalFormulaException{
      this.goal = goal;
      Proc = Solver.run(goal, services);
  }
  
  /** Interprets the result of the process.  
   * @return A instance of SMTSolverResult.
   * @throws IOException
   */
  public SMTSolverResult interpretAnswer() throws IOException
  {
      SMTSolverResult toReturn;
	try {
	    toReturn = Solver.interpretAnswer(Text, ErrorText, exitValue);
	} catch (IllegalArgumentException e) {
	    //the interpretation found an error.
	    throw new RuntimeException("Error while executing solver:\n" + e.getMessage());
	}
     return toReturn;
  }
    
}

/**
 * Implements the <code>BuildInRule</code> for the rule 'multiple provers', which allows the user for starting several external provers at the same time.
 */
public class SMTRuleMulti implements BuiltInRule, MakesProgress {
    
    
    private static final Logger logger = Logger
    .getLogger(AbstractSMTSolver.class.getName());
    /**If true, all provers must stop or the timeout must be reached, before the results are interpreted*/
    private boolean        waitForAllProvers=false;
    

    /**List of all possibles solvers that can be used, not installed solvers are also stored in <code>Solvers</code>*/
    private ArrayList<SolverWrapper> Solvers = new ArrayList<SolverWrapper>();
    /**List of all processes that has been started while executing the rule.*/
    private ArrayList<Process> runningProcesses = new ArrayList<Process>();
    /**List of all solvers that has been started while executing the rule.*/
    private ArrayList<SolverWrapper> runningSolvers = new ArrayList<SolverWrapper>(); 
    
    /**True, if the process of proving should be interrupted immediately. */
    private boolean toBeInterrupted = false;
    
    /**List of all listeners which watch the progress of proving.*/
    private ArrayList<ProgressMonitor> progressMonitors = new ArrayList<ProgressMonitor>();
    
    public void addProgressMonitor(ProgressMonitor p) {
	progressMonitors.add(p);
    }
    
    public boolean removeProgressMonitor(ProgressMonitor p) {
	return progressMonitors.remove(p);
    }
    
    public void removeAllProgressMonitors() {
	while (progressMonitors.size() > 0) {
	    progressMonitors.remove(0);
	}
    }
    
    public void interrupt() {
	this.toBeInterrupted = true;
    }
    
    
    /** Searches for the given <code>SMTSolver s</code> in <code>Solvers</code>  
     * @param s  SMTSolver to look for.
     * @return SolverWrapper that is associated with the given SMTSolver, or null when not found.
     */
    private SolverWrapper find(SMTSolver s)
    {
	for(SolverWrapper sw : Solvers)
	   if(s.name().equals(sw.getSolver().name())) return sw;
	return null;
    }
    
    
    
    /**
     * Finds the <code>SolverWrapper</code> associated with the process <code>p</code> 
     * @param p
     * 
     */
    private SolverWrapper find(Process p){
	for(SolverWrapper sw : Solvers)
	    if(sw.getProc() == p) return sw;
	return null;
    }
    
    /**
     * Finds the <code>SolverWrapper</code> associated with <code>name</code> 
     * @param name
     * 
     */
    private SolverWrapper find(String name)    {
	for(SolverWrapper sw: Solvers)
	    if(sw.getSolver().name().equals(name)) return sw;
	return null;
    }
    
    
    
    /**
     * This method sets, whether the SMTSolver s is executed by the rule or not.
     * @param s 
     * @param use true, if the SMTSolver s should be used, when the rule is executed
     */
    public void useSMTSolver(SMTSolver s, boolean use){
	SolverWrapper sw = find(s);
	if(sw == null) throw new IllegalArgumentException("Solver can not be found.");
	sw.setUsedForProving(use);
    }
    
    /**
     * This method sets, whether the SMTSolver s is executed by the rule or not.
     * @param name name of the solver
     * @param use true, if the SMTSolver should be used, when the rule is executed
     */
    public void useSMTSolver(String name, boolean use){
	SolverWrapper sw = find(name);
	if(sw == null) throw new IllegalArgumentException("There is no solver called "+ name);
	sw.setUsedForProving(use);
    }
    
    /** 
     * @return returns a list of all possible solvers, that are implemented by the interface SMTSolver
     */
    
    public ArrayList<String> getNamesOfSolvers(){
	ArrayList<String> list = new ArrayList<String>();
	for(SolverWrapper sw : Solvers){
	    list.add(sw.getSolver().name());
	}
	return list;
	
    }
    
    
    /**
     * returns whether the SMTSolver s is used by the rule.
     * @param s
     * @return true, if the SMTSolver s is used.
     */
    public boolean SMTSolverIsUsed(SMTSolver s){
	SolverWrapper sw = find(s);
	if(sw == null) throw new IllegalArgumentException("Solver can not be found.");
	return sw.isUsedForProving();
    }
    
    /**
     * returns whether the SMTSolver, specified by name, is uset by the rule
     * @param name name of the solver
     * @return true, if the solver is used
     */
    public boolean SMTSolverIsUsed(String name){
	SolverWrapper sw = find(name);
	if(sw == null) throw new IllegalArgumentException("Solver can not be found.");
	return sw.isUsedForProving();
    }
 
    
    /**
     * Constructor for the rule SMTRuleMulti
     * @param sl ArrayList of all possible provers. Possible means also provers that are not installed yet.
     */
    public SMTRuleMulti(ArrayList<SMTSolver> sl){
	
	for(SMTSolver s : sl)
	   Solvers.add(new SolverWrapper(s));
    }
    
    

    public boolean isWaitingForAllProvers() {
	    return waitForAllProvers;
	  }

        
    
    public void setWaitForAllProvers(boolean waitForAllProvers) {
	    this.waitForAllProvers = waitForAllProvers;
	  }

    /**
     *  @return returns true, if at least one installed solver is selected for the rule 'multiple provers' 
     */
    public boolean isUsable() {
	for(SolverWrapper sw : Solvers)
	    if(sw.isUsedForProving() && sw.getSolver().isInstalled(false)) return true;
	return false;
    }
    
    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }
    
    
    private void killProcesses(){
	for(Process p : runningProcesses)
	    p.destroy();
    }
    
   
    /**
     * Standard procedure for handling exceptions.
     * @param services Services object to get the exception handler
     * @param e  Exception to handle.
     */
    private void handleException(Services services,Exception e){
        if (services.getExceptionHandler() != null) {
	    services.getExceptionHandler().reportException(e);
		} else {
		    RuntimeException re = new RuntimeException(e.getMessage());
		    re.initCause(e);
		    throw re;
			}
	
    }
    
    /**
     * Cleans up the leaving of a proving.
     */
    private void clean(){
	runningProcesses.clear();
	runningSolvers.clear();
	toBeInterrupted = false;
	
    }

    
    /** 
     * @return returns null, when all provers have failed<br>
     *          returns <code>SLListOfGoal.EMPTY_LIST</code>, when one prover succeeded and the other provers haven't finished yet. 
     * 
     */
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
	int timeout = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getTimeout()*100;

	clean();	
	
	// Start the provers
	for(SolverWrapper sw : Solvers){
		try {
		    if(sw.isUsedForProving() && sw.getSolver().isInstalled(false)){
			sw.run(goal, services);
			runningProcesses.add(sw.getProc());
			runningSolvers.add(sw);
			sw.setFinished(false);
			
		    }
		    
		    
		} 
		catch (IllegalFormulaException ife){
		   handleException(services,ife);
		}
		
		catch (IOException ioe) {	    	    
		    handleException(services,ioe);	    
		}
	  
	}
	
	 
	 // initialize the ExecutionWatchDog and start the Timer
	 ExecutionWatchDog execWatch = new ExecutionWatchDog(timeout,runningProcesses);
	 Timer t = new Timer();
	 t.schedule(execWatch, new Date(System.currentTimeMillis()), 300);


	 
	 int count = 0;
	 int startedProcesses = runningProcesses.size();
	
	
	 try {
		//wait for the SMTSolver Thread and make popagate progress
		boolean finished = false;
		
		
		while (!finished&&runningProcesses.size()>0) {
		    //if there is a interruption signal, interrupt execWatch, 
		    if (this.toBeInterrupted) {
			this.toBeInterrupted = false;
			execWatch.interrupt();
			
		    }
		        ArrayList<Process> toRemove = new ArrayList<Process>();
			for(Process p : runningProcesses){
			    synchronized(p) {
				try{
				   
				   p.wait(300);
				   p.exitValue();
				   // if the program comes to this point, the process p stopped.
				   SolverWrapper sw = find(p);
				   if(sw.hasFinished()) continue;
				   toRemove.add(p);
				
				   try{
				       if(!execWatch.wasInterruptedByTimeout() && 
					   !execWatch.wasInterruptedByUser())
				       sw.setFinished(true);
				       count++;
				   }
				   catch(IOException ioe)
				   {
				       
				       handleException(services,ioe);
				   }
				if((!this.waitForAllProvers && sw.getResult().isValid() != ThreeValuedTruth.UNKNOWN) || 
				   (this.waitForAllProvers && count == startedProcesses) ||
				   execWatch.wasInterruptedByTimeout() ||
				   execWatch.wasInterruptedByUser()){
				    	finished =true;
				    	break;
				   }
				}catch (IllegalThreadStateException e) {
				    	//if the program comes to this point the provers are still running
					for (ProgressMonitor pm : this.progressMonitors) {
					    
					    pm.setProgress(execWatch.getProgress());
					}
				}
				
				
			    }		
			}
			runningProcesses.removeAll(toRemove);

		}
		
	    } catch (InterruptedException f) {
		logger.debug(
			"Process for smt formula proving interrupted.",
			f);
	    } finally {
		t.cancel();
		killProcesses();
		execWatch = null;
	    }
	    
	    if (count == 0) {
		
		//the solving was interrupted and no prover has finished. So return unknown
		return null;
	    } else {
		
		boolean notValid = false;
		boolean valid    = false;
		for(SolverWrapper sw : runningSolvers){
		    SMTSolverResult res;
		    if(sw.hasFinished()){
		      	res = sw.getResult();
		      	if(res.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE) notValid = true;
			if(res.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) valid = true;
			
			    
		    }
		    
	
		}
		// makes only sense when waitForAllProvers is true.
		if(notValid && valid) { throw new RuntimeException("One prover says true, the other prover says false!");}
		
		if(valid && !notValid) return ImmutableSLList.<Goal>nil();
		
	    }
	
	return null;

    }

    public String displayName() {

	String s = "multiple provers";
	int count =0;
	for(SolverWrapper sw : Solvers)
	    if(sw.isUsedForProving() && sw.getSolver().isInstalled(false)){
		s = s + (count==0 ? ": " : ", ");
		s = s + sw.getSolver().name();
		count++;
	    }
		
	return s;
	    
    }

    public Name name() {
	return new Name(displayName());
    }

}
