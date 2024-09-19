package org.key_project.isabelletranslation;

import org.jetbrains.annotations.NotNull;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;

public class IsabelleLauncher {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    private final IsabelleTranslationSettings settings;
    private IsabelleLauncherListener listener;

    private Thread shutdownResources;


    private final List<IsabelleSolver> runningSolvers = Collections.synchronizedList(new ArrayList<>());


    private final LinkedBlockingDeque<IsabelleSolver> solverQueue = new LinkedBlockingDeque<>();
    private final Collection<IsabelleSolver> solverSet = new HashSet<>();


    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) throws IOException {
        this.settings = settings;
    }

    public void try0ThenSledgehammerAllPooled(List<IsabelleProblem> problems, long timeoutSeconds, int instanceCount) throws IOException {
        IsabelleResourceController resourceController = new IsabelleResourceController(instanceCount);

        ExecutorService executorService = Executors.newFixedThreadPool(instanceCount);

        shutdownResources = new Thread(() -> {
            executorService.shutdownNow();
            resourceController.shutdownGracefully();
        });
        Runtime.getRuntime().addShutdownHook(shutdownResources);

        for (int i = 0; i < problems.size(); i++) {
            IsabelleSolver solver = new IsabelleSolverInstance(problems.get(i), List.of(new IsabelleSolverListener[0]), i, resourceController);
            solver.setTimeout(timeoutSeconds);
            solverQueue.add(solver);
            solverSet.add(solver);
        }

        listener.launcherStarted(this, solverSet);

        resourceController.init();
        listener.launcherPreparationFinished(this, solverSet);

        if (problems.isEmpty()) {
            return;
        }
        //Ensure the preamble theory is present
        TranslationAction.writeTranslationFiles(problems.get(0));


        Collection<Callable<List<SledgehammerResult>>> tasks = launchSolverInstances(instanceCount);

        LOGGER.info("Setup complete, starting {} problems...", problems.size());

        try {
            executorService.invokeAll(tasks);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } catch (RejectedExecutionException e) {
            //Launcher has been shutdown before running instances
            //Nothing to do here, intended behavior
        } finally {
            shutdown();
        }
    }

    private @NotNull Collection<Callable<List<SledgehammerResult>>> launchSolverInstances(int instanceCount) {
        Collection<Callable<List<SledgehammerResult>>> tasks = new LinkedBlockingDeque<>();

        for (int i = 0; i < instanceCount; i++) {
            tasks.add(() -> {
                IsabelleSolver solver;
                while ((solver = solverQueue.poll()) != null) {
                    runningSolvers.add(solver);
                    solver.start(null, settings);
                    runningSolvers.remove(solver);
                }
                return null;
            });
        }
        return tasks;
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
        shutdown();
        runningSolvers.forEach((solver) -> solver.interrupt(reasonOfInterruption));
        solverQueue.forEach((solver) -> solver.interrupt(reasonOfInterruption));

        runningSolvers.clear();
        solverQueue.clear();
        listener.launcherStopped(this, solverSet);
    }
}
