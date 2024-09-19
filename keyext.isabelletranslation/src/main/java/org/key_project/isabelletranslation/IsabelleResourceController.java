package org.key_project.isabelletranslation;

import de.unruh.isabelle.control.Isabelle;
import de.unruh.isabelle.control.IsabelleMLException;
import de.unruh.isabelle.java.JIsabelle;
import de.unruh.isabelle.mlvalue.ListConverter;
import de.unruh.isabelle.mlvalue.MLFunction2;
import de.unruh.isabelle.mlvalue.MLFunction3;
import de.unruh.isabelle.mlvalue.MLValue;
import de.unruh.isabelle.pure.Implicits;
import de.unruh.isabelle.pure.Position;
import de.unruh.isabelle.pure.Theory;
import de.unruh.isabelle.pure.TheoryHeader;
import org.slf4j.LoggerFactory;
import org.slf4j.Logger;
import scala.collection.immutable.List;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.*;

public class IsabelleResourceController {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleResourceController.class);
    private final LinkedBlockingQueue<IsabelleResource> idleInstances;

    private final IsabelleTranslationSettings settings;

    private boolean isShutdown = false;

    private final Collection<IsabelleSolver> waitingSolvers;

    private final int numberOfInstances;


    private final ExecutorService instanceCreatorService;



    public IsabelleResourceController(int numberOfInstances) {
        settings = IsabelleTranslationSettings.getInstance();
        idleInstances = new LinkedBlockingQueue<>(numberOfInstances);
        waitingSolvers = new HashSet<>();
        this.numberOfInstances = numberOfInstances;
        instanceCreatorService = Executors.newFixedThreadPool(numberOfInstances);
    }

    public void init() throws IOException {
        for (int i = 0; i < numberOfInstances; i++) {
            IsabelleResource newResource = createIsabelleResource();
            if (!isShutdown() && newResource != null) {
                idleInstances.add(newResource);
            }
        }
    }

    public IsabelleResource getIsabelleResource(IsabelleSolver requestingSolver) throws InterruptedException {
        waitingSolvers.add(requestingSolver);
        IsabelleResource freeResource = idleInstances.take();
        waitingSolvers.remove(requestingSolver);
        return freeResource;
    }

    public void shutdownGracefully() {
        isShutdown = true;

        instanceCreatorService.shutdownNow();

        waitingSolvers.forEach((x) -> x.interrupt(IsabelleSolver.ReasonOfInterruption.Exception));
        waitingSolvers.clear();

        idleInstances.forEach(IsabelleResource::destroy);
        idleInstances.clear();
    }

    public void returnResource(IsabelleSolver returningSolver, IsabelleResource resource) {
        assert resource != null;

        if (isShutdown()) {
            if (!resource.isDestroyed()) {
                //TODO some kind of race condition happens here
                resource.destroy();
            }
            return;
        }

        if (resource.isDestroyed()) {
            try {
                resource = createIsabelleResource();
            } catch (IOException e) {
                //Should not occur. If it was possible to create instances during creation, it should be possible now.
                shutdownGracefully();
                LOGGER.error(e.getMessage());
            }
        } else {
            resource.interrupt();
        }
        idleInstances.offer(resource);
    }

    public boolean isShutdown() {
        return isShutdown;
    }

    private IsabelleResource createIsabelleResource() throws IOException {
        Callable<IsabelleResource> creationTask = () -> {
            Isabelle isabelleInstance = startIsabelleInstance();
            Theory theory = beginTheory(isabelleInstance, settings);
            return new IsabelleResource(isabelleInstance, theory);
        };
        try {
            return instanceCreatorService.submit(creationTask).get();
        } catch (InterruptedException e) {
            shutdownGracefully();
            throw new RuntimeException(e);
        } catch (ExecutionException e) {
            if (e.getCause() instanceof IOException) {
                throw (IOException) e.getCause();
            }
            if (isShutdown()) {
                return null;
            }
            LOGGER.error("Error during Isabelle setup");
            throw new RuntimeException(e);
        } catch (RejectedExecutionException e) {
            //IsabelleResourceController is shutdown
            return null;
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

    private static Theory beginTheory(Isabelle isabelle, IsabelleTranslationSettings settings) {
        MLFunction3<Path, TheoryHeader, List<Theory>, Theory> begin_theory =
                MLValue.compileFunction("fn (path, header, parents) => Resources.begin_theory path header parents", isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
        MLFunction2<String, Position, TheoryHeader> header_read = MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter(), Implicits.theoryHeaderConverter());



        TheoryHeader header = header_read.apply(settings.getHeader(), Position.none(isabelle), isabelle, de.unruh.isabelle.mlvalue.Implicits.stringConverter(), Implicits.positionConverter())
                .retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
        Path topDir = settings.getTranslationPath();


        return begin_theory.apply(topDir, header, header.imports(isabelle).map((String name) -> Theory.apply(name, isabelle)), isabelle,
                        Implicits.pathConverter(), Implicits.theoryHeaderConverter(), new ListConverter<>(Implicits.theoryConverter()))
                .retrieveNow(Implicits.theoryConverter(), isabelle);
    }

    public record IsabelleResource(Isabelle instance, Theory theory) {
        public boolean isDestroyed() {
            return instance.isDestroyed();
        }

        void destroy() {
            instance.destroy();
        }

        private void interruptIntern() throws IsabelleMLException {
            instance.executeMLCodeNow("error \"Interrupt\"");
        }

        public void interrupt() {
            try {
                interruptIntern();
            } catch (IsabelleMLException e) {
                //Always throws this due to the way Isabelle is interrupted.
            }
        }
    }
}
