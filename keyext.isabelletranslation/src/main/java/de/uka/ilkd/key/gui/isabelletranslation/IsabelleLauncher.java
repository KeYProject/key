package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.util.Pair;
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
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingDeque;

public class IsabelleLauncher {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleLauncher.class);

    private final IsabelleTranslationSettings settings;

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

    public void try0ThenSledgehammerAllPooled(List<IsabelleProblem> problems, long timeoutSeconds, int coreCount) throws IOException {
        ExecutorService executorService = Executors.newFixedThreadPool(coreCount);
        Collection<Callable<List<SledgehammerResult>>> tasks = new LinkedBlockingDeque<>();
        LinkedBlockingDeque<Pair<Isabelle, Theory>> resourceInstances = new LinkedBlockingDeque<>();
        LinkedBlockingDeque<IsabelleProblem> problemsQueue = new LinkedBlockingDeque<>(problems);

        Thread shutdownResources = new Thread(() -> {
            for (Pair<Isabelle, Theory> resources : resourceInstances) {
                resources.first.destroy();
            }
            executorService.shutdown();
        });
        Runtime.getRuntime().addShutdownHook(shutdownResources);

        if (problems.isEmpty()) {
            return;
        }
        TranslationAction.writeTranslationFiles(problems.get(0));

        for (int i = 0; i < coreCount; i++) {
            Isabelle isabelle = startIsabelleInstance();
            Theory thy0 = beginTheory(settings.getTranslationPath(), isabelle);
            resourceInstances.add(new Pair<>(isabelle, thy0));

            tasks.add(() -> {
                IsabelleProblem problem;
                Pair<Isabelle, Theory> resources;
                while ((problem = problemsQueue.poll()) != null && (resources = resourceInstances.poll()) != null) {
                    problem.try0ThenSledgehammer(resources.first, resources.second, timeoutSeconds);
                    resourceInstances.add(resources);
                }
                return null;
            });
        }

        LOGGER.info("Setup complete, solver starting {} problems...", problems.size());

        try {
            executorService.invokeAll(tasks);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        } finally {
            shutdownResources.run();
            Runtime.getRuntime().removeShutdownHook(shutdownResources);
        }
    }

    private Isabelle startIsabelleInstance() throws IOException {
        ArrayList<Path> sessionRoots = new ArrayList<>();
        sessionRoots.add(settings.getTranslationPath());
        Isabelle isabelle;
        try {
            Isabelle.Setup setup = JIsabelle.setupSetLogic("KeYTranslations",
                    JIsabelle.setupSetSessionRoots(sessionRoots,
                            JIsabelle.setupSetWorkingDirectory(settings.getTranslationPath(),
                                    JIsabelle.setup(settings.getIsabellePath()))));
            isabelle = new Isabelle(setup);
        } catch (Exception e) {
            LOGGER.error("Can't find Isabelle at {}", settings.getIsabellePath());
            throw new IOException("Can't find Isabelle at " + settings.getIsabellePath());
        }
        return isabelle;
    }
}
