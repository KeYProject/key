package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.lang.reflect.InvocationTargetException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Timer;
import java.util.TimerTask;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.SMTSolver.SolverState;
import de.uka.ilkd.key.smt.SMTSolverResult.ThreeValuedTruth;

public class SolverListener implements SolverLauncherListener {
    private ProgressDialog2 progressDialog;
    private ProgressPanel2 [] progressPanels;
    private Collection<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
    private Timer timer = new Timer();
   
    private static final int RESOLUTION = 1000;
    
    private class InternSMTProblem{
	final int problemIndex;
	final int solverIndex;
	final SMTSolver solver;
	final SMTProblem problem;
	
	public InternSMTProblem(int problemIndex, int solverIndex, SMTProblem problem, SMTSolver solver) {
	    super();
	    this.problemIndex = problemIndex;
	    this.solverIndex = solverIndex;
	    this.problem = problem;
	    this.solver  = solver;
        }
	
	public int getSolverIndex() {
	    return solverIndex;
        }
	
	public int getProblemIndex() {
	    return problemIndex;
        }
	
    }

    

    
    @Override
    public void launcherStopped() {
	timer.cancel();
	refreshDialog();
	progressDialog.setStopButtonEnabled(false);
	System.out.println("Launcher stopped");
    }
    
    private void prepareDialog(Collection<SMTProblem> smtProblems,
	                         Collection<SolverType> solverTypes,
	                         final SolverLauncher launcher){
	
	progressPanels = new ProgressPanel2[solverTypes.size()];
	String names[] = new String[smtProblems.size()];
	int x =0; 
	for(SMTProblem problem: smtProblems){
	    int y=0; 
	    for(SMTSolver solver : problem.getSolvers()){
		this.problems.add(new InternSMTProblem(x,y,problem,solver));
		y++;
	    }
	    names[x]=problem.getName();
	    x++;
	}
	
	
	int i=0; 
	for(SolverType factory : solverTypes){
	    progressPanels[i]= new ProgressPanel2(factory.getName(), smtProblems.size(),
		    RESOLUTION,names);
	    i++;
	}
	

	progressDialog = new ProgressDialog2(progressPanels,
		new ActionListener() {
		    
		    @Override
		    public void actionPerformed(ActionEvent e) {
			discardEvent(launcher);
		    }
		},
		new ActionListener() {
		    
		    @Override
		    public void actionPerformed(ActionEvent e) {
			applyEvent(launcher);			
		    }
		}, new ActionListener() {		    
		    @Override
		    public void actionPerformed(ActionEvent e) {
			stopEvent(launcher);	
		    }
		});
	progressDialog.setVisible(true);	
    }
    
    private void stopEvent(final SolverLauncher launcher){
	launcher.stop();
    }
    
    private void discardEvent(final SolverLauncher launcher){
	launcher.stop();
    }
    
    private void applyEvent(final SolverLauncher launcher){
	launcher.stop();  
    }
    
    @Override
    public void launcherStarted(final Collection<SMTProblem> smtProblems,
	                         final Collection<SolverType> solverTypes,
	                         final SolverLauncher launcher){
	
	//SwingUtilities.invokeLater(new Runnable() {
	    
	  //  @Override
	    //public void run() {
	    	prepareDialog(smtProblems, solverTypes, launcher);
		
	    //}
	//});



	

	timer.schedule(new TimerTask() {
	    @Override
	    public void run() {
		refreshDialog();
	    }
	},0,10);
    }
    
    private void refreshDialog(){
	for(InternSMTProblem problem : problems){
	    refreshProgessOfProblem(problem);
	}
    }
    
    private long calculateProgress(InternSMTProblem problem){
	long maxTime = problem.solver.getTimeout();
	long startTime = problem.solver.getStartTime();
	long currentTime = System.currentTimeMillis();
	
	
	return RESOLUTION-((startTime-currentTime)*RESOLUTION)/maxTime;
    }
    
    private float calculateRemainingTime(InternSMTProblem problem){
	long startTime = problem.solver.getStartTime();
	long currentTime = System.currentTimeMillis();
	long temp = (startTime-currentTime)/100;
	return Math.max((float)temp/10.0f,0);
    }
    
    private ProgressPanel2 getPanel(InternSMTProblem problem){
	
	return progressPanels[problem.getSolverIndex()];
	
    }

    
    private boolean refreshProgessOfProblem(InternSMTProblem problem){
	SolverState state = problem.solver.getState();
	switch(state){
	case Running:
	    running(problem);
	    return true;
	case Stopped:
	    stopped(problem);
	    return false;
	case Waiting:
	    waiting(problem);
	    return true;
	
	}
	return true;
	
    }
    
    
    private void waiting(InternSMTProblem problem){
 	
     }
    
    private void running(InternSMTProblem problem){
	int problemIndex = problem.getProblemIndex();
	long progress = calculateProgress(problem);
	getPanel(problem).setProgress(problemIndex,(int)progress);
	float remainingTime = calculateRemainingTime(problem);
	getPanel(problem).setText(problemIndex, Float.toString(remainingTime)+" sec.");
    }
	
    
    
    private void stopped(InternSMTProblem problem){
	if(problem.solver.wasInterrupted()){
	    interrupted(problem);
	}else if(problem.solver.getFinalResult().isValid() 
		  == ThreeValuedTruth.TRUE){
	    successfullyStopped(problem);
	}else if(problem.solver.getFinalResult().isValid() 
		  == ThreeValuedTruth.FALSIFIABLE){
	   unsuccessfullyStopped(problem);
	}else{
	   unknownStopped(problem);
	}
    }
    
    
    private void interrupted(InternSMTProblem problem){
	int problemIndex = problem.getProblemIndex();
	ReasonOfInterruption reason = problem.solver.getReasonOfInterruption();
	switch(reason){
	case Exception:
	    getPanel(problem).setText(problemIndex,"Exception.");
	    break;
	case NoInterruption:
	    throw new RuntimeException("This position should not be reachable!");
	    
	case Timeout:
	    getPanel(problem).setProgress(problemIndex,RESOLUTION);		
	    getPanel(problem).setText(problemIndex,"Timeout.");
	    break;
	case User:
	    getPanel(problem).setText(problemIndex,"Interrupted by user.");
	    break;	
	}	
    }
    
    private void successfullyStopped(InternSMTProblem problem){
	int problemIndex = problem.getProblemIndex();
	getPanel(problem).setColor(problemIndex, Color.GREEN);
	getPanel(problem).setText(problemIndex,"Solved.");
    }
    
    private void unsuccessfullyStopped(InternSMTProblem problem){
	int problemIndex = problem.getProblemIndex();
	getPanel(problem).setColor(problemIndex, Color.RED);
	getPanel(problem).setText(problemIndex,"Falsifiable.");
	
    }
    
    private void unknownStopped(InternSMTProblem problem){
	int problemIndex = problem.getProblemIndex();		
	getPanel(problem).setText(problemIndex,"Unkown.");
    }
 
    

    @Override
    public void processInterrupted(SMTSolver solver, SMTProblem problem,
	    Throwable e) { }

    @Override
    public void processStarted(SMTSolver solver, SMTProblem problem) { }

    @Override
    public void processStopped(SMTSolver solver, SMTProblem problem) {
	//refreshDialog();
    }

    @Override
    public void processTimeout(SMTSolver solver, SMTProblem problem) {


    }

    @Override
    public void processUser(SMTSolver solver, SMTProblem problem) {


    }



}
