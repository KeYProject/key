package org.key_project.isabelletranslation.automation;

import org.jspecify.annotations.NonNull;
import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.TranslationAction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.*;
import java.util.concurrent.*;

public class IsabelleLauncher implements IsabelleSolverListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    private final IsabelleTranslationSettings settings;
    private IsabelleLauncherListener listener;

    private Thread shutdownResources;

    private ExecutorService executorService;


    private final List<IsabelleSolver> runningSolvers = Collections.synchronizedList(new ArrayList<>());


    private final LinkedBlockingDeque<IsabelleSolver> solverQueue = new LinkedBlockingDeque<>();
    private final Collection<IsabelleSolver> solverSet = new HashSet<>();
    private IsabelleSolver.ReasonOfInterruption reasonOfInterruption;


    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) throws IOException {
        this.settings = settings;
    }

    public void try0ThenSledgehammerAllPooled(List<IsabelleProblem> problems, int timeoutSeconds, int instanceCount) throws IOException {
        if (problems.isEmpty()) {
            return;
        }

        //Ensure the preamble theory is present
        problems.get(0).writeTranslationFiles(settings);

        IsabelleResourceController resourceController = new IsabelleResourceController(instanceCount);

        executorService = Executors.newFixedThreadPool(instanceCount);

        shutdownResources = new Thread(() -> {
            executorService.shutdown();
            resourceController.shutdownGracefully();
        });
        Runtime.getRuntime().addShutdownHook(shutdownResources);

        for (int i = 0; i < problems.size(); i++) {
            IsabelleSolver solver = new IsabelleSledgehammerSolver(problems.get(i), List.of(this), i, resourceController, settings);
            solver.setTimeout(timeoutSeconds);

            solverQueue.add(solver);
            solverSet.add(solver);
        }

        listener.launcherStarted(this, solverSet);

        resourceController.init();
        listener.launcherPreparationFinished(this, solverSet);

        LOGGER.info("Setup complete, starting {} problems...", problems.size());

        try {
            executorService.invokeAll(solverQueue);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } catch (RejectedExecutionException e) {
            //Launcher has been shutdown before running instances
            //Nothing to do here, intended behavior
        } finally {
            shutdown();
        }

        listener.launcherStopped(this, solverSet);
    }

    private void shutdown() {
        Runtime.getRuntime().removeShutdownHook(shutdownResources);
        if (shutdownResources.getState() == Thread.State.NEW) {
            shutdownResources.start();
        }
    }

    public void addListener(IsabelleLauncherListener listener) {
        this.listener = listener;
    }

    public void stopAll(IsabelleSolver.ReasonOfInterruption reasonOfInterruption) {
        this.reasonOfInterruption = reasonOfInterruption;

        shutdown();

        executorService.shutdownNow();

        solverQueue.forEach(solver -> solver.interrupt(reasonOfInterruption));
        solverQueue.clear();

        runningSolvers.forEach(solver -> {
            if (reasonOfInterruption != null) {
                solver.interrupt(reasonOfInterruption);
            }
        });
        runningSolvers.clear();

        listener.launcherStopped(this, solverSet);
    }

    @Override
    public void processStarted(IsabelleSolver solver, IsabelleProblem problem) {
        runningSolvers.add(solver);
        solverQueue.remove(solver);
    }

    @Override
    public void processError(IsabelleSolver solver, IsabelleProblem problem, Exception e) {
        runningSolvers.remove(solver);
        if (reasonOfInterruption != null) {
            solver.interrupt(reasonOfInterruption);
        }
    }

    @Override
    public void processStopped(IsabelleSolver solver, IsabelleProblem problem) {
        runningSolvers.remove(solver);
    }
}
