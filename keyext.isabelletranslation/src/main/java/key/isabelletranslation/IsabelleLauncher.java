package key.isabelletranslation;

import org.key_project.util.collection.Pair;
import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.ListConverter;
import de.unruh.isabelle.mlvalue.MLFunction2;
import de.unruh.isabelle.mlvalue.MLFunction3;
import de.unruh.isabelle.mlvalue.MLValue;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Position;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.TheoryHeader;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Timer;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingDeque;

public class IsabelleLauncher {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    private final IsabelleTranslationSettings settings;
    private IsabelleLauncherListener listener;


    public IsabelleLauncher(@NonNull IsabelleTranslationSettings settings) throws IOException {
        this.settings = settings;
    }

    private Theory beginTheory(Path source, Isabelle isabelle) {
        MLFunction3<Path, TheoryHeader, scala.collection.immutable.List<Theory>, Theory> begin_theory =
                MLValue.compileFunction("fn (path, header, parents) => Resources.begin_theory path header parents", isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
        MLFunction2<String, Position, TheoryHeader> header_read = MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter(), Implicits.theoryHeaderConverter());

        TheoryHeader header = header_read.apply("theory Translation imports Main KeYTranslations.TranslationPreamble begin", Position.none(isabelle), isabelle, de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter())
                .retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
        Path topDir = source.getParent();
        return begin_theory.apply(topDir, header, header.imports(isabelle).map((String name) -> Theory.apply(name, isabelle)), isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()))
                .retrieveNow(Implicits.theoryConverter(), isabelle);
    }

    public void try0ThenSledgehammerAllPooled(List<IsabelleProblem> problems, long timeoutSeconds, int instanceCount) throws IOException {
        listener.launcherStarted(this, problems);
        ExecutorService executorService = Executors.newFixedThreadPool(instanceCount);
        Collection<Callable<List<SledgehammerResult>>> tasks = new LinkedBlockingDeque<>();
        LinkedBlockingDeque<IsabelleSolver> solverQueue = new LinkedBlockingDeque<>();


        IsabelleResourceController resourceController = new IsabelleResourceController(instanceCount);

        Thread shutdownResources = new Thread(() -> {
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
                    solver.start(null, settings);
                }
                return null;
            });
        }

        LOGGER.info("Setup complete, starting {} problems...", problems.size());

        try {
            executorService.invokeAll(tasks);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } finally {
            shutdownResources.start();
            Runtime.getRuntime().removeShutdownHook(shutdownResources);
        }
    }

    public void addListener(IsabelleLauncherListener listener) {
        this.listener = listener;
    }
}
