/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Semaphore;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

/**
 * IN ORDER TO START THE SOLVERS USE THIS CLASS.<br>
 * There are two cases how the solvers can be started:<br>
 * <br>
 * 1. Case: Starting the solvers synchronously<br>
 * <br>
 * First Step: Create the SMT problem:<br>
 * <code>SMTProblem problem = new SMTProblem(g); // g can be either a goal or term</code> <br>
 * <br>
 * Second Step: Create the launcher object:<br>
 * <code>SolverLauncher launcher = new SolverLauncher(new SMTSettings(){...});</code> <br>
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
 * </pre>
 *
 * <br>
 * <p>
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
 *            }
 *          }
 *          public void launcherStarted(Collection<SMTProblem> problems,
 *                                      Collection<SolverType> solverTypes,
 *                                      SolverLauncher launcher);
 *             });
 *   launcher.launch(problem,services,SolverType.Z3_SOLVER,SolverType.YICES_SOLVER);
 *
 *            }
 *        });
 *    thread.start();
 * </pre>
 *
 * <br>
 * NOTE: In case that you add at least one listener to a launcher no exception is thrown when a
 * solver produces an error. The exceptions of the solvers are stored within the solver object and
 * can be accessed by <code>solver.getException</code>.
 */

public class SolverLauncher {

    private ExecutorService threadPool;

    private Collection<SMTSolver> solvers;

    /* ############### Public Interface #################### */

    /**
     * Create for every solver execution a new object. Don't reuse the solver launcher object.
     *
     * @param settings settings for the execution of the SMT Solvers.
     */
    public SolverLauncher(SMTSettings settings) {
        this.settings = settings;
    }

    /**
     * Adds a listener to the launcher object. The listener can be used to observe the solver
     * execution. If at least one listener was added to the solver launcher, no exception is thrown
     * when a solver produces an error. The error can be read when the method
     * <code>launcherStopped</code> of the listener is called.
     */
    public void addListener(SolverLauncherListener listener) {
        listeners.add(listener);
    }

    public void removeListener(SolverLauncherListener listener) {
        listeners.remove(listener);
    }

    /**
     * Launches several solvers for the problem that is handed over.<br>
     * Note: Calling this methods does not create an extra thread, i.e. the calling thread is
     * blocked until the method returns. (Synchronous method call).
     *
     * @param problem The problem that should be translated and passed to the solvers
     * @param services The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(SMTProblem problem, Services services, SolverType... solverTypes) {
        checkLaunchCall();
        launchIntern(problem, services, solverTypes);
    }

    /**
     * Launches several solvers for the problems that are handed over. Note: Calling this methods
     * does not create an extra thread, i.e. the calling thread is blocked until the method returns.
     * (Synchronous method call).
     *
     * @param problems The problems that should be translated and passed to the solvers
     * @param services The services object of the current proof.
     * @param solverTypes A list of solver types that should be used for the problem.
     */
    public void launch(Collection<SolverType> solverTypes, Collection<SMTProblem> problems,
            Services services) {
        checkLaunchCall();
        launchIntern(solverTypes, problems, services);
    }

    /**
     * If all permits of the semaphore are acquired the launcher must be stopped.
     */
    private boolean isInterrupted() {
        return stopSemaphore.availablePermits() == 0;
    }

    /**
     * Stops the execution of the launcher.
     */
    public void stop() {
        solvers.forEach((solver) -> solver.interrupt(ReasonOfInterruption.User));
        if (threadPool != null) {
            threadPool.shutdownNow();
        }
        notifyListenersOfStop();
    }

    /* ################ Implementation ############################ */

    /**
     * The SMT settings that should be used
     */
    private final SMTSettings settings;

    /**
     * This semaphore is used for stopping the launcher. If the permit is acquired the launcher
     * stops.
     */
    private final Semaphore stopSemaphore = new Semaphore(1, true);

    private final LinkedList<SolverLauncherListener> listeners = new LinkedList<>();

    /**
     * Every launcher object should be used only once.
     */
    private boolean launcherHasBeenUsed = false;

    /**
     * Creates the concrete solver objects and distributes them to the SMT problems.
     */
    private void prepareSolvers(Collection<SolverType> factories, Collection<SMTProblem> problems,
            Services services) {
        threadPool = Executors.newFixedThreadPool(settings.getMaxConcurrentProcesses());
        this.solvers = new ArrayList<>();
        for (SMTProblem problem : problems) {
            for (SolverType factory : factories) {
                if (factory.isInstalled(false)) {
                    SMTSolver solver = factory.createSolver(problem, null, services, settings, settings.getTimeout(factory));
                    problem.addSolver(solver);
                    solvers.add(solver);
                }
            }
        }
    }

    private void launchIntern(SMTProblem problem, Services services, SolverType[] solverTypes) {
        LinkedList<SolverType> types = new LinkedList<>();
        Collections.addAll(types, solverTypes);
        LinkedList<SMTProblem> problems = new LinkedList<>();
        problems.add(problem);
        launchIntern(types, problems, services);
    }

    private void launchIntern(Collection<SolverType> factories, Collection<SMTProblem> problems,
            Services services) {
        // consider only installed solvers.
        LinkedList<SolverType> installedSolvers = new LinkedList<>();
        for (SolverType type : factories) {
            if (type.isInstalled(false)) {
                installedSolvers.add(type);
                if (settings.checkForSupport()) {
                    type.checkForSupport();
                }
            }
        }
        prepareSolvers(installedSolvers, problems, services);
        launchIntern(problems, installedSolvers);
    }

    private void checkLaunchCall() {
        if (launcherHasBeenUsed) {
            throw new IllegalStateException("Every launcher object can be used only once.");
        }
        launcherHasBeenUsed = true;
    }

    private void launchIntern(Collection<SMTProblem> problems, Collection<SolverType> factories) {

        LinkedList<SMTSolver> solvers = new LinkedList<>();
        for (SMTProblem problem : problems) {
            solvers.addAll(problem.getSolvers());
        }
        launchSolvers(solvers, problems, factories);
    }

    private void launchSolvers(Queue<SMTSolver> solvers, Collection<SMTProblem> problems,
            Collection<SolverType> solverTypes) {
        // Show progress dialog
        notifyListenersOfStart(problems, solverTypes);

        // Launch all solvers until the queue is empty or the launcher is
        // interrupted.
        launchLoop(solvers);

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
     * Core of the launcher. Start all solvers until the queue is empty or the launcher is
     * interrupted.
     */
    private void launchLoop(Queue<SMTSolver> solvers) {
        // as long as there are jobs to do, start solvers
        try {
            threadPool.invokeAll(solvers);
        } catch (InterruptedException e) {
            launcherInterrupted(e);
            notifyListenersOfStop();
        }
    }

    /**
     * In case of that the user has interrupted the execution the reason of interruption must be
     * set.
     */
    private void cleanUp(Collection<SMTSolver> solvers) {
        if (isInterrupted()) {
            for (SMTSolver solver : solvers) {
                solver.interrupt(ReasonOfInterruption.User);
            }
        }
        threadPool.shutdown();
    }

    private void notifyListenersOfStop() {
        Collection<SMTSolver> finishedSolvers = new ArrayList<>(solvers.stream().filter((solver) -> solver.getState() == SMTSolver.SolverState.Stopped).toList());

        for (SMTSolver solver : solvers) {
            if (!finishedSolvers.contains(solver)) {
                finishedSolvers.add(solver);
            }
        }

        for (SolverLauncherListener listener : listeners) {
            listener.launcherStopped(this, finishedSolvers);
        }

        if (solvers.size() != finishedSolvers.size() && listeners.isEmpty()) {
            throw new SolverException(solvers);
        }
    }

    /**
     * If there is some exception that is caused by the launcher (not by the solvers) just forward
     * it
     */
    private void launcherInterrupted(Exception e) {
        throw new RuntimeException(e);
    }
}
