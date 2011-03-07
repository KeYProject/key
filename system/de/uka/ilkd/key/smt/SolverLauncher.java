package de.uka.ilkd.key.smt;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import javax.swing.SwingUtilities;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.strategy.FIFOStrategy.Factory;






class SolverTimeout extends TimerTask{
    static int counter =0;
    int id = ++counter;
    final SMTSolver solver;
    final Session   session;
    final long     timeout;
    public SolverTimeout(SMTSolver solver, Session session, long timeout){
	this.solver = solver;
	this.session = session;
	this.timeout = timeout;
    }
    
    public SolverTimeout(SMTSolver solver, long timeout){
	this.solver = solver;
	this.session = null;
	this.timeout = timeout;
    }
    
    
    @Override
    public void run() {
	System.out.println("Timeout "+ id);
	if(session != null){
	    session.interruptSolver(solver,ReasonOfInterruption.Timeout);	
	}else{
	    solver.interrupt(ReasonOfInterruption.Timeout);
	}
	//this.cancel();
    }
    
    public long getTimeout() {
	return timeout;
    }
    
}

interface SolverListener{
    void processStarted(SMTSolver solver, SMTProblem problem);
    void processInterrupted(SMTSolver solver, SMTProblem problem, Throwable e);
    void processStopped(SMTSolver solver, SMTProblem problem);
    void processTimeout(SMTSolver solver, SMTProblem problem);
    void processUser(SMTSolver solver, SMTProblem problem);
}

class Session{

    
     private ReentrantLock lock = new ReentrantLock();
     private LinkedList<SMTSolver> currentlyRunning = new LinkedList<SMTSolver>();
     public void addCurrentlyRunning(SMTSolver solver){
	 lock.lock();
	 currentlyRunning.add(solver);
	 lock.unlock();
     }
     
     public void removeCurrentlyRunning(SMTSolver solver){
	 lock.lock();
	 int i= currentlyRunning.indexOf(solver);
	 if(i >=0){
	     currentlyRunning.remove(i);		     
	 }
	 
	 lock.unlock();
     }
     
     public int getCurrentlyRunningCount(){
	 lock.lock();
	 int count = currentlyRunning.size();
	 lock.unlock();
	 return count;
     }
     
     public void interruptSolver(SMTSolver solver, ReasonOfInterruption reason){
	 lock.lock();
	 Iterator<SMTSolver> it = currentlyRunning.iterator();
	 while(it.hasNext()){
	     SMTSolver next = it.next();
	     if(next.equals(next)){
		 next.interrupt(reason);
		 it.remove();
		 break;
	     }
	 }
	 lock.unlock();
     }
     
     public void interruptAll(ReasonOfInterruption reason){
	 lock.lock();
	 for(SMTSolver solver : currentlyRunning){
	     solver.interrupt(reason);
	 }
	 lock.unlock();
     }
	    
}
public class SolverLauncher implements SolverListener {
    private final static int PERIOD = 50;
    private final ReentrantLock lock = new ReentrantLock();
    private final Condition     wait = lock.newCondition();
    private final Timer         timer = new Timer(true);
    private final Session session = new Session();
    private final SMTSettings   settings;
    private final Semaphore     stopSemaphore = new Semaphore(1,true);
    

    private LinkedList<SolverLauncherListener> listeners = new LinkedList<SolverLauncherListener>();
    
    
    public SolverLauncher(SMTSettings settings){
	this.settings = settings;
    }
    
    public void addListener(SolverLauncherListener listener){
	listeners.add(listener);
    }
    
    public void removeListener(SolverLauncherListener listener){
	listeners.remove(listener);
    }
    
    
    public void launch(Collection<SolverType> factories, Collection<SMTProblem> problems,
	    Services services){
	
	LinkedList<SolverType> installedSolvers = new LinkedList<SolverType>();
	for(SolverType type: factories){
	    if(type.isInstalled(false)){
		installedSolvers.add(type);
	    }
	}
	problems = prepareSolvers(installedSolvers, problems,services);
	
	launch(problems,installedSolvers);	
    }
    

    
    private Collection<SMTProblem> prepareSolvers(Collection<SolverType> factories,  Collection<SMTProblem> problems,
	    Services services){
	
	for(SMTProblem problem : problems){
	    for(SolverType factory : factories){
		if(factory.isInstalled(false)){
		    SMTSolver solver = factory.createSolver(problem,this,services);
		    problem.addSolver(solver);
		}
	    }
	}
	return problems;
    }
    
    private void launch(Collection<SMTProblem> problems, Collection<SolverType> factories){
	LinkedList<SMTSolver> solvers = new LinkedList<SMTSolver>();
	for(SMTProblem problem : problems){
	    solvers.addAll(problem.getSolvers());
	}
	launchSolvers(solvers, problems,factories);
    }
    
    private void fillRunningList(LinkedList<SMTSolver> solvers, Session session){
	int i=0; 
	while(startNextSolvers(solvers, session) && !isInterrupted()){
	    SMTSolver solver = solvers.poll();
	    final SolverTimeout solverTimeout = new SolverTimeout(solver,session,settings.getTimeout()+i*50);
	    timer.schedule(solverTimeout,settings.getTimeout(),PERIOD);
   
	    session.addCurrentlyRunning(solver);
	    solver.start(solverTimeout,settings);
	    i++;
	
	}
    }
    
    private boolean isInterrupted(){
	return stopSemaphore.availablePermits() == 0;
    }
    
    private boolean startNextSolvers(LinkedList<SMTSolver> solvers, Session session){
	return !solvers.isEmpty() && 
	        session.getCurrentlyRunningCount() < settings.getMaxConcurrentProcesses();
    }
    
    private void launchSolvers(LinkedList<SMTSolver> solvers,
	                        Collection<SMTProblem> problems,
	                        Collection<SolverType> solverTypes){
	
	
	notifyListenersOfStart(problems, solverTypes);
	
	launchLoop(solvers);
	
	// at this point either there are no solvers left to start or
	// the whole launching process was interrupted.	
	waitForRunningSolvers();
	
	cleanUp(solvers);
	
	notifyListenersOfStop();
	
    }
    
    private void notifyListenersOfStart(Collection<SMTProblem> problems,
            				  Collection<SolverType> solverTypes){
	for(SolverLauncherListener listener : listeners){
	    listener.launcherStarted(problems,solverTypes,this);
	}
    }
    
    
    private void launchLoop(LinkedList<SMTSolver> solvers){
	// as long as there are jobs to do, start solvers
	while(!solvers.isEmpty() && !isInterrupted()){
	   lock.lock(); 
	   try{
	   fillRunningList(solvers,session);
	   if(!startNextSolvers(solvers, session) && 
	       !isInterrupted()){
	       try {
	        wait.await();
        
            } catch (InterruptedException e) {
        	launcherInterrupted(e);
            }
	   }}
	   finally{
	   lock.unlock();
	   }
	}
    }
    
    private void waitForRunningSolvers(){
	while(session.getCurrentlyRunningCount() > 0){
	    lock.lock(); 
	       try {
		        wait.await();
	            } catch (InterruptedException e) {
	        	launcherInterrupted(e);
	            }finally{
	    lock.unlock();
	   }
	}
    }
    
    private void cleanUp(Collection<SMTSolver> solvers){
	if(isInterrupted()){
	    for(SMTSolver solver : solvers){
		solver.interrupt(ReasonOfInterruption.User);
	    }
	}
    }
    
    private void notifyListenersOfStop(){
	for(SolverLauncherListener listener : listeners){
	    listener.launcherStopped();
	}
    }


    
    private void notifySolverHasFinished(SMTSolver solver){
	lock.lock();
	session.removeCurrentlyRunning(solver);
	wait.signal();
	lock.unlock();
    }
    
    public void stop(){
	stopSemaphore.tryAcquire();
	session.interruptAll(ReasonOfInterruption.User);
    }
    
     
    private void launcherInterrupted(Exception e){
	System.out.println("launcher interrupted");

    }

    @Override
    public void processStarted(SMTSolver solver, SMTProblem problem) {

	for(SolverLauncherListener listener : listeners){
	    listener.processStarted(solver, problem);
	}
    }

    @Override
    public void processStopped(SMTSolver solver, SMTProblem problem) {

	notifySolverHasFinished(solver);	
	for(SolverLauncherListener listener : listeners){
	    listener.processStopped(solver, problem);
	}
    }

    @Override
    public void processInterrupted(SMTSolver solver, SMTProblem problem,
            Throwable e) {

	e.printStackTrace();
	notifySolverHasFinished(solver);
	for(SolverLauncherListener listener : listeners){
	    listener.processInterrupted(solver, problem, e);
	}
    }

    @Override
    public void processTimeout(SMTSolver solver, SMTProblem problem) {
	

	notifySolverHasFinished(solver);
	for(SolverLauncherListener listener : listeners){
	    listener.processTimeout(solver, problem);
	}
	
    }

    @Override
    public void processUser(SMTSolver solver, SMTProblem problem) {

	for(SolverLauncherListener listener : listeners){
	    listener.processUser(solver, problem);
	}
	
    }


    
    

}
