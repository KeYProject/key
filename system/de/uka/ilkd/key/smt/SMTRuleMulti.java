package de.uka.ilkd.key.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Timer;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.SLListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
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
  private SMTSolverResult Result = null;
  /**If true, the solver is used for proving*/
  private boolean 	   UsedForProving=false;
  
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

  public Process getProc() {
    return Proc;
  }

  public SMTSolver getSolver() {
    return Solver;
  }

  
  public void run(Goal goal, Services services) throws IOException, IllegalFormulaException{
      Proc = Solver.run(goal, services);
  }
  
  /** Interprets the result of the process.  
   * @return 
   * @throws IOException
   */
  public SMTSolverResult interpretAnswer() throws IOException
  {
      SMTSolverResult toReturn;
      InputStream in = Proc.getInputStream();
      String text = AbstractSMTSolver.read(in);
      in.close();
	
      in = Proc.getErrorStream();
      String error = AbstractSMTSolver.read(in);
      in.close();
	try {
	    toReturn = Solver.interpretAnswer(text, error, Proc.exitValue());
	} catch (IllegalArgumentException e) {
	    //the interpretation found an error.
	    throw new RuntimeException("Error while executing solver:\n" + e.getMessage());
	}
     return toReturn;
  }
    
}

public class SMTRuleMulti implements BuiltInRule {
    
    
    private static final Logger logger = Logger
    .getLogger(AbstractSMTSolver.class.getName());
    
    

    /**List of all possibles solvers that can be used, not installed solvers are also stored in <code>Solvers</code>*/
    private ArrayList<SolverWrapper> Solvers = new ArrayList<SolverWrapper>();
    /**List of all processes that has been started while executing the rule*/
    private ArrayList<Process> runningProcesses = new ArrayList<Process>();
    /**List of all solvers that has been started while executing the rule*/
    private ArrayList<SolverWrapper> runningSolvers = new ArrayList<SolverWrapper>(); 
    
    /** Searches for the given <code>SMTSolver s</code> in <code>Solvers</code>  
     * @param s  
     * @return 
     */
    private SolverWrapper find(SMTSolver s)
    {
	for(SolverWrapper sw : Solvers)
	   if(s.name().equals(sw.getSolver().name())) return sw;
	return null;
    }
    
    /**
     * This method sets, whether the SMTSolver s is executed by the rule or not.
     * @param s 
     * @param use true, if the SMTSolver s should be used, when the rule is executed
     */
    public void useSMTSolver(SMTSolver s, boolean use)
    {
	SolverWrapper sw = find(s);
	if(sw == null) throw new IllegalArgumentException("Solver can not be found.");
	sw.setUsedForProving(use);
    }
    
    /**
     * returns whether the SMTSolver s is used by the rule.
     * @param s
     * @return true, if the SMTSolver s is used.
     */
    public boolean SMTSolverIsUsed(SMTSolver s)
    {
	SolverWrapper sw = find(s);
	if(sw == null) throw new IllegalArgumentException("Solver can not be found.");
	return sw.isUsedForProving();

    }
    
 


    
    /**
     * Constructor for the rule SMTRuleMulti
     * @param sl ArrayList of all possible provers. Possible means also provers that are not installed yet.
     */
    public SMTRuleMulti(ArrayList<SMTSolver> sl)
    {
	
	for(SMTSolver s : sl)
	   Solvers.add(new SolverWrapper(s));
    }

    
    
    public boolean isApplicable(Goal goal, PosInOccurrence pio,
	    Constraint userConstraint) {
	//only make applicable, if the complete goal should be proved
	return pio == null;
    }

    
    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
	int timeout = ProofSettings.DEFAULT_SETTINGS.getDecisionProcedureSettings().getTimeout()*100;
	SMTSolverResult result = SMTSolverResult.NO_IDEA;
	runningProcesses.clear();
	runningProcesses.clear();
	
	for(SolverWrapper sw : Solvers){
		try {
		    if(sw.isUsedForProving() && sw.getSolver().isInstalled(false)){
			sw.run(goal, services);
			runningProcesses.add(sw.getProc());
			runningSolvers.add(sw);
		    }
		    
		    
		} 
		catch (IllegalFormulaException ife)
		{
		    //TODO handle exception 
		}
		
		catch (IOException ioe) {	    	    
		if (services.getExceptionHandler() != null) {
		    services.getExceptionHandler().reportException(ioe);
		} else {
		    RuntimeException re = new RuntimeException(ioe.getMessage());
		    re.initCause(ioe);
		    throw re;
			}	    
		}
	  
	}
	
	 
	 ExecutionWatchDog execWatch = new ExecutionWatchDog(timeout,runningProcesses);
	 
	 Timer t = new Timer();
	 t.schedule(execWatch, new Date(System.currentTimeMillis()), 300);


	 
	
	 boolean interruptedByWatchdog = false;
	 try {
		//wait for the SMTSolver Thread and make popagate progress
		boolean finished = false;
		
		//synchronized (p) {
		while (!finished) {
		   /* if (this.toBeInterrupted) {
			this.toBeInterrupted = false;
			execWatch.interrupt();
			
		    }*/
		    try {
			for(Process p : runningProcesses){
			    synchronized(p) {
				p.wait(300);
				p.exitValue();
			    }		
			}
			 			 
			//if the program comes here, p has been finished.
			finished = true;
		    } catch (IllegalThreadStateException e) {
			//if program comes here, p has not been finished yet.
			//update the progress.
			//for (ProgressMonitor pm : this.progressMonitors) {
			  //  pm.setProgress(execWatch.getProgress());
			//}
		    }
		}
		//}
		if (execWatch.wasInterruptedByTimeout()) {
		    interruptedByWatchdog = true;
		    logger.debug(
		    "Process for smt formula proving interrupted because of timeout.");
		} else if (execWatch.wasInterruptedByUser()) {
		    interruptedByWatchdog = true;
		    logger.debug(
		    "Process for smt formula proving interrupted because of user interaction.");
		}
	    } catch (InterruptedException f) {
		logger.debug(
			"Process for smt formula proving interrupted.",
			f);
	    } finally {
		t.cancel();
		execWatch = null;
	    }
	    
	    if (interruptedByWatchdog) {
		
		//the solving was interrupted. So return unknown
		return null;
	    } else {
		
		boolean notValid = false;
		boolean valid    = false;
		for(SolverWrapper sw : runningSolvers)
		{
		    SMTSolverResult res;
		    try{
			res = sw.interpretAnswer();
			if(res.isValid() == SMTSolverResult.ThreeValuedTruth.FALSE) notValid = true;
			if(res.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) valid = true;
		    }
		    catch(IOException ioe) {}
		    
	
		}
		
		if(notValid && valid) { /*TODO insert exception */}
		
		if(valid && !notValid) return SLListOfGoal.EMPTY_LIST;
		
	    }
	return null;

    }

    public String displayName() {

	    return "multiple provers";
    }

    public Name name() {
	return new Name(displayName());
    }

}
