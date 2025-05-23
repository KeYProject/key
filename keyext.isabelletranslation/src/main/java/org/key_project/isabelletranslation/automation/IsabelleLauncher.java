/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.gui.controller.IsabelleLauncherProgressDialogMediator;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class allows for the launch of automated proof searches in Isabelle for a list of isabelle
 * problems.
 */
public class IsabelleLauncher implements IsabelleSolverListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    /**
     * The settings used during proof search in Isabelle.
     */
    private final IsabelleTranslationSettings settings;

    /**
     * The listener objects for this launcher.
     * Is used to control the Isabelle dialog with {@link IsabelleLauncherProgressDialogMediator}.
     */
    private final List<IsabelleLauncherListener> listeners = new ArrayList<>();

    /**
     * The thread, that will be called on shutdown of KeY to ensure there are no runaway Isabelle
     * instances or open ThreadPools
     */
    private Thread shutdownResources;

    /**
     * The ExecutorService used to call the solver instances.
     */
    private ExecutorService executorService;

    /**
     * The list of currently running solver instances.
     */
    private final List<IsabelleSolver> runningSolvers =
        Collections.synchronizedList(new ArrayList<>());

    /**
     *
     */
    private final List<IsabelleSolver> finishedSolvers =
        Collections.synchronizedList(new ArrayList<>());

    /**
     * The queue of solver instances that have not started yet.
     */
    private final LinkedBlockingDeque<IsabelleSolver> solverQueue = new LinkedBlockingDeque<>();


    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) {
        this.settings = settings;
    }

    /**
     * Launches the given problems with the specified timeout using a specified number of concurrent
     * Isabelle instances
     *
     * @param problems The problems for which proof search will be started
     * @param timeoutSeconds The timeout setting to use for the Isabelle instances
     * @param instanceCount The number of concurrent Isabelle instances
     * @throws IOException translation files could not be written
     * @throws IsabelleNotFoundException If {@link IsabelleResourceController} fails to initiate
     */
    public void launch(List<IsabelleProblem> problems, int timeoutSeconds,
            int instanceCount) throws IOException, IsabelleNotFoundException {
        // Ensure the preamble theory file is present, so theory objects can be created.
        // If no problems have translations, don't write anything
        // All solvers should recognize this and throw an appropriate exception
        List<IsabelleProblem> problemsWithTranslation =
            problems.stream().filter(IsabelleProblem::hasTranslation).toList();

        if (!problemsWithTranslation.isEmpty()) {
            problemsWithTranslation.get(0).writeTranslationFiles(settings);
        }


        IsabelleResourceController resourceController =
            new IsabelleResourceController(instanceCount, settings);

        executorService = Executors.newFixedThreadPool(instanceCount);

        shutdownResources = new Thread(() -> {
            executorService.shutdown();
            resourceController.shutdownGracefully();
            finishedSolvers.clear();
        });
        Runtime.getRuntime().addShutdownHook(shutdownResources);

        for (int i = 0; i < problems.size(); i++) {
            IsabelleSolver solver = new IsabelleSledgehammerSolver(problems.get(i), List.of(this),
                i, resourceController, settings);
            solver.setTimeout(timeoutSeconds);

            solverQueue.add(solver);
        }

        notifyLauncherStarted();

        try {
            resourceController.init();
        } catch (InterruptedException e) {
            stopAll();
            notifyLauncherStopped();
            return;
        }
        notifyPreparationFinished();

        LOGGER.info("Setup complete, starting {} problems...", problems.size());

        try {
            executorService.invokeAll(solverQueue);
        } catch (InterruptedException e) {
            stopAll();
        } catch (RejectedExecutionException e) {
            // Launcher has been shutdown before running instances
            // Nothing to do here, intended behavior
        } finally {
            shutdown();
        }

        notifyLauncherStopped();
    }

    /**
     * Notifies all listeners of the launcher stop.
     */
    private void notifyLauncherStopped() {
        listeners.forEach(listener -> listener.launcherStopped(this, finishedSolvers));
    }

    /**
     * Notifies all listeners that the launcher has finished preparations.
     * This usually means the Isabelle instances have been created by the
     * {@link IsabelleResourceController}.
     */
    private void notifyPreparationFinished() {
        listeners.forEach(listener -> listener.launcherPreparationFinished(this, finishedSolvers));
    }

    /**
     * Notifies all listeners that the launcher has started.
     */
    private void notifyLauncherStarted() {
        listeners.forEach(listener -> listener.launcherStarted(this, new ArrayList<>(solverQueue)));
    }

    /**
     * Starts the shutdownResources thread, if it was not started already.
     * Also removes the shutdown hook.
     */
    private void shutdown() {
        Runtime.getRuntime().removeShutdownHook(shutdownResources);
        if (shutdownResources.getState() == Thread.State.NEW) {
            shutdownResources.start();
        }
    }

    /**
     * Adds a listener. Primarily used for {@link IsabelleLauncherProgressDialogMediator} to update
     * the Isabelle dialog.
     *
     * @param listener The listener to be used
     */
    public void addListener(IsabelleLauncherListener listener) {
        listeners.add(listener);
    }

    /**
     * Calls the {@link #shutdown()} function. Then stops the execution of all
     * {@link IsabelleSolver} instances that were not started.
     * Also interrupts all running solvers. Can be used to perform a user initiated interrupt when
     * using IsabelleSolver.ReasonOfInterruption.User.
     */
    public void stopAll() {
        shutdown();

        executorService.shutdownNow();

        solverQueue.forEach(IsabelleSolver::abort);
        solverQueue.clear();

        runningSolvers.forEach(IsabelleSolver::abort);
        runningSolvers.clear();

        notifyLauncherStopped();

        finishedSolvers.clear();
    }

    @Override
    public void processStarted(IsabelleSolver solver, IsabelleProblem problem) {
        runningSolvers.add(solver);
        if (!solverQueue.remove(solver)) {
            LOGGER.error(
                "Something went wrong during Isabelle instance management! Solver \"{}\" was not in queue, but started anyway.",
                solver.name() + ": " + solver.getProblem().getName());
            stopAll();
            throw new RuntimeException("Something went wrong during Isabelle instance management!");
        }
    }

    @Override
    public void processError(IsabelleSolver solver, IsabelleProblem problem, Exception e) {
        runningSolvers.remove(solver);
        finishedSolvers.add(solver);
    }

    @Override
    public void processStopped(IsabelleSolver solver, IsabelleProblem problem) {
        runningSolvers.remove(solver);
        finishedSolvers.add(solver);
    }
}
