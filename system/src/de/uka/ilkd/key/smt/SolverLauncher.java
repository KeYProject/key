// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

import java.util.*;
import java.util.concurrent.Semaphore;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.java.Services;

import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;

/**
 * IN ORDER TO START THE SOLVERS USE THIS CLASS.<br>
 * There are two cases how the solvers can be started:<br>
 * <br>
 * 1. Case: Starting the solvers synchronously<br>
 *<br>
 * First Step: Create the SMT problem:<br>
 * <code>SMTProblem problem = new SMTProblem(g); // g can be either a goal or term</code>
 * <br>
 * <br>
 * Second Step: Create the launcher object:<br>
 * <code>SolverLauncher launcher = new SolverLauncher(new SMTSettings(){...});</code>
 * <br>
 * <br>
 * Third Step: Launch the solvers you want to execute<br>
 * <code>launcher.launch(problem, services,SolverType.Z3_SOLVER,SolverType.YICES_SOLVER);</code>
 * <br>
 * <br>
 * Forth Step: Get the final result<br>
 * <code>return problem.getFinalResult();</code><br>
 * <br>
 * In case that you want to access the result of each solver:<br>
 * 
 * <pre>
 * for (SMTSolver solver : problem.getSolvers()) {
 *     solver.getFinalResult();
 * }
 *</pre>
 * 
 * <br>
 * 
 * 2. Case: Starting the solvers asynchronously:<br>
 * <br>
 * 
 * <pre>
 * Thread thread = new Thread(new Runnable() {        
 * public void run() {
 *   SMTProblem final problem = new SMTProblem(...);
 *   SolverLauncher launcher = new SolverLauncher(new SMTSettings(...));
 *   launcher.addListener(new SolverLauncherListener(){
 *          public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> problemSolvers){
 *          	// do something with the results here...
 *          	problem.getFinalResult();
 *          	// handling the problems that have occurred:
 *          	for(SMTSolver solver : problemSolvers){
 *          		solver.getException();
 *          		...
 *          	}
 *          }
 *          public void launcherStarted(Collection<SMTProblem> problems,
 *                                      Collection<SolverType> solverTypes,
 *                                      SolverLauncher launcher);
 *     		 });
 *   launcher.launch(problem,services,SolverType.Z3_SOLVER,SolverType.YICES_SOLVER);
 * 	      
 * 	        }
 * 	    });
 *    thread.start();
 *</pre>
 * 
 * <br>
 *NOTE: In case that you add at least one listener to a launcher no exception
 * is thrown when a solver produces an error. The exceptions of the solvers are
 * stored within the solver object and can be accessed by
 * <code>solver.getException</code>.
 */

public class SolverLauncher implements SolverListener {

    /* ############### Public Interface #################### */
    /**
     * Create for every solver execution a new object. Don't reuse the solver
     * launcher object.
     * 
     * @param settings
     *            settings for the execution of the SMT Solvers.
     */
    public SolverLauncher(SMTSettings settings) {
	this.settings = settings;

    }

    /**
     * Adds a listener to the launcher object. The listener can be used to
     * observe the solver execution. If at least one listener was added to the
     * solver launcher, no exception is thrown when a solver produces an error.
     * The error can be read when the method <code>launcherStopped</code> of the
     * listener is called.
     * */
    public void addListener(SolverLauncherListener listener) {
	listeners.add(listener);
    }

    public void removeListener(SolverLauncherListener listener) {
	listeners.remove(listener);
    }

    /**
     * Launches several solvers for the problem that is handed over.<br>
     * Note: Calling this methods does not create an extra thread, i.e. the
     * calling thread is blocked until the method returns. (Synchronous method
     * call).
     * 
     * @param problem
     *            The problem that should be translated and passed to the
     *            solvers
     * @param services
     *            The services object of the current proof.
     * @param solverTypes
     *            A list of solver types that should be used for the problem.
     * 
     */
    public void launch(SMTProblem problem, Services services,
	    SolverType... solverTypes) {
	checkLaunchCall();
	launchIntern(problem, services, solverTypes);
    }

    /**
     * Launches several solvers for the problems that are handed over. Note:
     * Calling this methods does not create an extra thread, i.e. the calling
     * thread is blocked until the method returns. (Synchronous method call).
     * 
     * @param problems
     *            The problems that should be translated and passed to the
     *            solvers
     * @param services
     *            The services object of the current proof.
     * @param solverTypes
     *            A list of solver types that should be used for the problem.
     */
    public void launch(Collection<SolverType> solverTypes,
	    Collection<SMTProblem> problems, Services services) {
	checkLaunchCall();
	launchIntern(solverTypes, problems, services);
    }

    /**
     * Stops the execution of the launcher.
     */
    public void stop() {
	stopSemaphore.tryAcquire();
	session.interruptAll(ReasonOfInterruption.User);
    }

    /* ################ Implementation ############################ */

    /**
     * Period of a timer task. Sometimes it happens that a timer event got lost.
     * Therefore the timer tasks are called periodly until it is canceld
     */
    private final static int PERIOD = 50;

    /**
     * Used for synchronisation. This lock is used in the same way as the
     * <code>synchronize<code>statement.
     */
    private final ReentrantLock lock = new ReentrantLock();
    /**
     * This condition is used in order to make the launcher thread wait. The
     * launcher goes to sleep when no more solvers can be started and some other
     * solvers are still executed. Everytime a solver stops it sends a signal to
     * the <code>wait</code>-condition in order to wake up the launcher.
     */
    private final Condition wait = lock.newCondition();
    /** The timer that is responsible for the timeouts. */
    private final Timer timer = new Timer(true);
    /**
     * A sesion encapsulates some attributes that should be accessed only by
     * specified methods (in oder to maintain thread safety)
     */
    private final Session session = new Session();
    /** The SMT settings that should be used */
    private final SMTSettings settings;
    /**
     * This semaphore is used for stopping the launcher. If the permit is
     * acquired the launcher stops.
     */
    private final Semaphore stopSemaphore = new Semaphore(1, true);

    private LinkedList<SolverLauncherListener> listeners = new LinkedList<SolverLauncherListener>();

    /** Every launcher object should be used only once. */
    private boolean launcherHasBeenUsed = false;

    /**
     * Creates the concrete solver objects and distributes them to the SMT
     * problems.
     */
    private Collection<SMTProblem> prepareSolvers(
	    Collection<SolverType> factories, Collection<SMTProblem> problems,
	    Services services) {
	for (SMTProblem problem : problems) {
	    for (SolverType factory : factories) {
		if (factory.isInstalled(false)) {
		    SMTSolver solver = factory.createSolver(problem, this,
			    services);
		    problem.addSolver(solver);
		
		}
	    }
	}
	return problems;
    }

    private void launchIntern(SMTProblem problem, Services services,
	    SolverType[] solverTypes)  {

	LinkedList<SolverType> types = new LinkedList<SolverType>();
	Collections.addAll(types, solverTypes);
	LinkedList<SMTProblem> problems = new LinkedList<SMTProblem>();
	problems.add(problem);
	launchIntern(types, problems, services);
    }

    private void launchIntern(Collection<SolverType> factories,
	    Collection<SMTProblem> problems, Services services)
	    {

	// consider only installed solvers.
	LinkedList<SolverType> installedSolvers = new LinkedList<SolverType>();
	for (SolverType type : factories) {
	    if (type.isInstalled(false)) {
	    	installedSolvers.add(type);
	    	if(settings.checkForSupport()){
	    		type.checkForSupport();
	    	}
	    }
	}
	problems = prepareSolvers(installedSolvers, problems, services);

	launchIntern(problems, installedSolvers);
    }

    private void checkLaunchCall() {
	if (launcherHasBeenUsed) {
	    throw new RuntimeException(
		    "Every launcher object can be used only once.");
	}
	launcherHasBeenUsed = true;
    }

    private void launchIntern(Collection<SMTProblem> problems,
	    Collection<SolverType> factories)  {

	LinkedList<SMTSolver> solvers = new LinkedList<SMTSolver>();
	for (SMTProblem problem : problems) {
	    solvers.addAll(problem.getSolvers());
	}
	launchSolvers(solvers, problems, factories);
    }

    /**
     * Takes the next solvers from the queue and starts them. It depends on the
     * settings how many solvers can be executed concurrently.
     */
    private void fillRunningList(LinkedList<SMTSolver> solvers) {
	int i = 0;
	while (startNextSolvers(solvers) && !isInterrupted()) {
	    SMTSolver solver = solvers.poll();

	    SolverTimeout solverTimeout = new SolverTimeout(solver,
		    session, settings.getTimeout() + i * 50);

	 
	    timer.schedule(solverTimeout, settings.getTimeout(),PERIOD);
	    session.addCurrentlyRunning(solver);
	    // This cast is okay since there is only the class
	    // SMTSolverImplementation that implements SMTSolver.
	    ((SMTSolverImplementation) solver).start(solverTimeout, settings);
	    i++;

	}
    }

    /**
     * If all permits of the semaphore are acquired the launcher must be
     * stopped.
     */
    private boolean isInterrupted() {
	return stopSemaphore.availablePermits() == 0;
    }

    /**
     * Checks whether it is possible to start another solver.
     */
    private boolean startNextSolvers(LinkedList<SMTSolver> solvers) {
	return !solvers.isEmpty()
	        && session.getCurrentlyRunningCount() < settings
	                .getMaxConcurrentProcesses();
    }

    private void launchSolvers(LinkedList<SMTSolver> solvers,
	    Collection<SMTProblem> problems, Collection<SolverType> solverTypes)
    {

	notifyListenersOfStart(problems, solverTypes);

	// Launch all solvers until the queue is empty or the launcher is
	// interrupted.
	launchLoop(solvers);

	// at this point either there are no solvers left to start or
	// the whole launching process was interrupted.
	waitForRunningSolvers();

	cleanUp(solvers);

	notifyListenersOfStop();

    }

    private void notifyListenersOfStart(Collection<SMTProblem> problems,
	    Collection<SolverType> solverTypes) {
	for (SolverLauncherListener listener : listeners) {
	    listener.launcherStarted(problems, solverTypes, this);
	}
    }

    /**
     * Core of the launcher. Start all solvers until the queue is empty or the
     * launcher is interrupted.
     */
    private void launchLoop(LinkedList<SMTSolver> solvers) {
	// as long as there are jobs to do, start solvers
	while (!solvers.isEmpty() && !isInterrupted()) {
	    lock.lock();
	    try {
		// start solvers as many as possible
		fillRunningList(solvers);
		if (!startNextSolvers(solvers) && !isInterrupted()) {
		    try {
			// if there is nothing to do, wait for the next solver
			// finishing its task.
			wait.await();

		    } catch (InterruptedException e) {
			launcherInterrupted(e);
		    }
		}
	    } finally {
		lock.unlock();
	    }
	}
    }

    /**
     * The launcher should not be stopped until every solver has stopped.
     */
    private void waitForRunningSolvers() {
	while (session.getCurrentlyRunningCount() > 0) {
	    lock.lock();
	    try {
		wait.await();
	    } catch (InterruptedException e) {
		launcherInterrupted(e);
	    } finally {
		lock.unlock();
	    }
	}
    }

    /**
     * In case of that the user has interrupted the execution the reason of
     * interruption must be set.
     */
    private void cleanUp(Collection<SMTSolver> solvers) {
	if (isInterrupted()) {
	    for (SMTSolver solver : solvers) {
		solver.interrupt(ReasonOfInterruption.User);
	    }
	}
    }

    private void notifyListenersOfStop()  {
	Collection<SMTSolver> solvers = session.getProblemSolvers();
	for (SolverLauncherListener listener : listeners) {
	    listener.launcherStopped(this, solvers);
	}

	if (!solvers.isEmpty() && listeners.isEmpty()) {
	    throw new SolverException(solvers);
	}
    }

    /**
     * Is called when a solver has finished its task (Solver Thread). It removes
     * the solver from the list of the currently running solvers and tries to
     * wake up the launcher.
     */
    private void notifySolverHasFinished(SMTSolver solver) {
	lock.lock();
	try {
		session.removeCurrentlyRunning(solver);
		wait.signal();
	} finally {
		lock.unlock();
	}
    }

    /**
     * If there is some exception that is caused by the launcher (not by the
     * solvers) just forward it
     */
    private void launcherInterrupted(Exception e) {
	throw new RuntimeException(e);
    }

    @Override
    public void processStarted(SMTSolver solver, SMTProblem problem) {
    }

    @Override
    public void processStopped(SMTSolver solver, SMTProblem problem) {
	notifySolverHasFinished(solver);
    }

    @Override
    public void processInterrupted(SMTSolver solver, SMTProblem problem,
	    Throwable e) {
	session.addProblemSolver(solver);
	notifySolverHasFinished(solver);
    }

    @Override
    public void processTimeout(SMTSolver solver, SMTProblem problem) {
	notifySolverHasFinished(solver);
    }

    @Override
    public void processUser(SMTSolver solver, SMTProblem problem) {
    }

}

/**
 * The session class encapsulates some attributes that should be only accessed
 * by specified methods (in order to maintain thread safety)
 */
class Session {

    /** Locks the queue of the currently running solvers */
    private ReentrantLock lock = new ReentrantLock();
    /** Locks the collection of the problem solvers. */
    private ReentrantLock problemSolverLock = new ReentrantLock();
    private Collection<SMTSolver> problemSolvers = new LinkedList<SMTSolver>();
    private LinkedList<SMTSolver> currentlyRunning = new LinkedList<SMTSolver>();

    /** Adds a solver to the list of currently running solvers. Thread safe */
    public void addCurrentlyRunning(SMTSolver solver) {
	try {
	    lock.lock();
	    currentlyRunning.add(solver);
	} finally {
	    lock.unlock();
	}
    }

    public void removeCurrentlyRunning(SMTSolver solver) {
	try {
	    lock.lock();
	    int i = currentlyRunning.indexOf(solver);
	    if (i >= 0) {
		currentlyRunning.remove(i);
	    }
	} finally {
	    lock.unlock();
	}
    }

    public int getCurrentlyRunningCount() {
	try {
	    lock.lock();
	    int count = currentlyRunning.size();
	    return count;
	} finally { // finally trumps return
	    lock.unlock();
	}
    }

    public void interruptSolver(SMTSolver solver, ReasonOfInterruption reason) {
	try {
	    lock.lock();
	    Iterator<SMTSolver> it = currentlyRunning.iterator();
	    while (it.hasNext()) {
		SMTSolver next = it.next();
		if (next.equals(solver)) {
		    next.interrupt(reason);
		    it.remove();
		    break;
		}
	    }
	} finally {
	    lock.unlock();
	}
    }

    public void interruptAll(ReasonOfInterruption reason) {
	try {
	    lock.lock();
	    for (SMTSolver solver : currentlyRunning) {
		solver.interrupt(reason);
	    }
	} finally {
	    lock.unlock();
	}
    }

    public void addProblemSolver(SMTSolver solver) {
	try {
	    problemSolverLock.lock();
	    problemSolvers.add(solver);
	} finally {
	    problemSolverLock.unlock();
	}
    }

    public Collection<SMTSolver> getProblemSolvers() {
	try {
	    problemSolverLock.lock();
	    Collection<SMTSolver> copy = new LinkedList<SMTSolver>(
		    problemSolvers);
	    return copy; // finally trumps return
	} finally {
	    problemSolverLock.unlock();
	}

    }

}
