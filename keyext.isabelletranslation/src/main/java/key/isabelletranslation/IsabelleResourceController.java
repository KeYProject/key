package key.isabelletranslation;

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
import org.slf4j.LoggerFactory;
import org.slf4j.Logger;
import scala.collection.immutable.List;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.concurrent.LinkedBlockingQueue;

public class IsabelleResourceController {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleResourceController.class);
    private LinkedBlockingQueue<IsabelleResource> idleInstances;

    private IsabelleTranslationSettings settings;

    private boolean isShutdown = false;

    private Collection<IsabelleSolver> waitingSolvers;



    public IsabelleResourceController(int numberOfInstances) throws IOException {
        settings = IsabelleTranslationSettings.getInstance();
        idleInstances = new LinkedBlockingQueue<>(numberOfInstances);
        waitingSolvers = new HashSet<>();
        for (int i = 0; i < numberOfInstances; i++) {
            idleInstances.add(createIsabelleResource());
        }
    }

    public IsabelleResource getIsabelleResource(IsabelleSolver requestingSolver) throws InterruptedException {
        waitingSolvers.add(requestingSolver);
        return idleInstances.take();
    }

    public void shutdownGracefully() {
        isShutdown = true;

        waitingSolvers.forEach((x) -> x.interrupt(IsabelleSolver.ReasonOfInterruption.Exception));
        waitingSolvers.clear();

        idleInstances.forEach(IsabelleResource::destroy);
        idleInstances.clear();
    }

    public static IsabelleResource createIsabelleResourceFromInstance(Isabelle isabelle, IsabelleTranslationSettings settings) {
        Theory theory = beginTheory(isabelle, settings);
        return new IsabelleResource(isabelle, theory);
    }


    public void returnResource(IsabelleResource resource) {
        if (resource.isDestroyed()) {
            try {
                resource = createIsabelleResource();
            } catch (IOException e) {
                //Should not occur. If it was possible to create instances during creation, it should be possible now.
                shutdownGracefully();
                LOGGER.error(e.getMessage());
            }
        }
        resource.interrupt();
        idleInstances.offer(resource);
    }

    private IsabelleResource createIsabelleResource() throws IOException {
        Isabelle isabelleInstance = startIsabelleInstance();
        Theory theory = beginTheory(isabelleInstance, settings);
        return new IsabelleResource(isabelleInstance, theory);
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

        public void destroy() {
            instance.destroy();
        }

        public void interrupt() {
            instance.executeMLCodeNow("error \"Interrupt\"");
        }
    }
}