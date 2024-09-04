package key.isabelletranslation;

import org.key_project.util.collection.Pair;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.pure.Theory;
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


    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) throws IOException {
        this.settings = settings;
    }

    public void try0ThenSledgehammerAllPooled(List<IsabelleProblem> problems, long timeoutSeconds, int instanceCount) throws IOException {
        listener.launcherStarted(this, problems);
        ExecutorService executorService = Executors.newFixedThreadPool(instanceCount);
        Collection<Callable<List<SledgehammerResult>>> tasks = new LinkedBlockingDeque<>();


        IsabelleResourceController resourceController = new IsabelleResourceController(instanceCount);

        shutdownResources = new Thread(() -> {
            executorService.shutdown();
            resourceController.shutdownGracefully();
        });
        Runtime.getRuntime().addShutdownHook(shutdownResources);

        resourceController.init();

        if (problems.isEmpty()) {
            return;
        }
        //Ensure the preamble theory is present
        TranslationAction.writeTranslationFiles(problems.get(0));

        problems.forEach((problem) -> {
            IsabelleSolver solver = new IsabelleSolverInstance(problem, List.of(new IsabelleSolverListener[0]), resourceController);
            solver.setTimeout(timeoutSeconds);
            solverQueue.add(solver);
        });

        Timer timer = new Timer(true);

        for (int i = 0; i < instanceCount; i++) {
            tasks.add(() -> {
                IsabelleSolver solver;
                Pair<Isabelle, Theory> resources;
                while ((solver = solverQueue.poll()) != null) {
                    //IsabelleSolver.IsabelleSolverTimeout solverTimeout = new IsabelleSolver.IsabelleSolverTimeout(solver);
                    //timer.schedule(null, solver.getTimeout());
                    runningSolvers.add(solver);
                    solver.start(null, settings);
                    runningSolvers.remove(solver);
                }
                return null;
            });
        }

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
    }
}
