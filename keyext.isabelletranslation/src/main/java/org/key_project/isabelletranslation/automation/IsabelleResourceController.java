/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.concurrent.*;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;

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
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import scala.collection.immutable.List;

/**
 * This class handles creation of Isabelle instances, as well as providing methods for their
 * destruction.
 * This class also acts as a semaphore for Isabelle instances.
 * The Isabelle instances are bundled with a {@link Theory} into a {@link IsabelleResource} for this
 * purpose.
 */
public class IsabelleResourceController {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleResourceController.class);
    /**
     * The idle Isabelle instances.
     */
    private final LinkedBlockingQueue<IsabelleResource> idleInstances;

    /**
     * The settings to be used. Needed for path to Isabelle
     */
    private final IsabelleTranslationSettings settings;

    /**
     * Flag to check for shutdowns.
     */
    private boolean isShutdown = false;

    /**
     * Queue of threads waiting for Isabelle resources.
     */
    private final LinkedBlockingQueue<Thread> waitingThreads;

    /**
     * The number of Isabelle instances to create and store in this semaphore.
     */
    private final int numberOfInstances;

    /**
     * Thread pool for instance creation
     */
    private final ExecutorService instanceCreatorService;

    /**
     * Semaphore to ensure fairness when taking Isabelle instance.
     */
    private final Semaphore takeSemaphore;


    /**
     * Creates a resource controller. Initializes the settings.
     *
     * @param numberOfInstances the maximum number of Isabelle instances to create at any time
     * @param settings {@link IsabelleTranslationSettings} to be used
     */
    public IsabelleResourceController(int numberOfInstances, IsabelleTranslationSettings settings) {
        this.settings = settings;
        idleInstances = new LinkedBlockingQueue<>(numberOfInstances);
        waitingThreads = new LinkedBlockingQueue<>();
        this.numberOfInstances = numberOfInstances;
        instanceCreatorService = Executors.newFixedThreadPool(numberOfInstances);
        takeSemaphore = new Semaphore(1, true);
    }

    /**
     * Creates the Isabelle instances.
     *
     * @throws IsabelleNotFoundException If instance creation failed.
     */
    public void init() throws IsabelleNotFoundException, InterruptedException {
        for (int i = 0; i < numberOfInstances; i++) {
            if (!isShutdown()) {
                IsabelleResource newResource = createIsabelleResource();
                idleInstances.add(newResource);
            }
        }
    }

    /**
     * Tries to acquire a Isabelle instance. Fairness is ensured by a semaphore.
     *
     * @return an idle Isabelle resource
     * @throws InterruptedException if the thread is interrupted while waiting
     */
    public IsabelleResource getIsabelleResource() throws InterruptedException {
        waitingThreads.add(Thread.currentThread());
        takeSemaphore.acquire();
        try {
            return idleInstances.take();
        } finally {
            waitingThreads.remove(Thread.currentThread());
            takeSemaphore.release();
        }
    }

    /**
     * Calls {@link ExecutorService#shutdownNow()} for the instance creator service thereby stopping
     * instance creation.
     * <p>
     * Interrupts all waiting threads.
     * <p>
     * Destroys all idle instances.
     */
    public void shutdownGracefully() {
        isShutdown = true;

        instanceCreatorService.shutdownNow();

        waitingThreads.forEach(Thread::interrupt);
        waitingThreads.clear();

        idleInstances.forEach(IsabelleResource::destroy);
        idleInstances.clear();
    }

    /**
     * Adds a resource to the queue. The resource is interrupted via
     * {@link IsabelleResource#interrupt()} to ensure it is idle.
     * <p>
     * If the controller is shutdown the resource is destroyed instead.
     *
     * @param resource the resource to return
     */
    public void returnResource(IsabelleResource resource) {
        assert resource != null;

        if (isShutdown()) {
            if (!resource.isDestroyed()) {
                resource.destroy();
            }
            return;
        }

        if (resource.isDestroyed()) {
            try {
                resource = createIsabelleResource();
            } catch (IsabelleNotFoundException e) {
                // Should not occur. If it was possible to create instances during creation, it
                // should be possible now.
                shutdownGracefully();
                LOGGER.error(e.getMessage());
            } catch (InterruptedException e) {
                shutdownGracefully();
                LOGGER.error(e.getMessage());
                Thread.currentThread().interrupt();
            }
        } else {
            resource.interrupt();
        }
        idleInstances.offer(resource);
    }

    /**
     * Checks if the controller is shutdown.
     *
     * @return true - controller is shutdown, false - otherwise
     */
    public boolean isShutdown() {
        return isShutdown;
    }

    /**
     * Creates a new {@link IsabelleResource} via the thread pool used for this purpose.
     *
     * @return fresh IsabelleResource
     * @throws IsabelleNotFoundException if instance creation failed
     */
    private IsabelleResource createIsabelleResource()
            throws IsabelleNotFoundException, InterruptedException {
        Callable<IsabelleResource> creationTask = () -> {
            Isabelle isabelleInstance = startIsabelleInstance();
            Theory theory = beginTheory(isabelleInstance, settings);
            return new IsabelleResourceImpl(isabelleInstance, theory);
        };
        try {
            return instanceCreatorService.submit(creationTask).get();
        } catch (ExecutionException e) {
            LOGGER.error("Error during Isabelle setup");

            if (e.getCause() instanceof IsabelleNotFoundException) {
                throw (IsabelleNotFoundException) e.getCause();
            }
            if (e.getCause() instanceof InterruptedException) {
                throw (InterruptedException) e.getCause();
            }
            throw new RuntimeException(e);
        } catch (RejectedExecutionException e) {
            throw new RuntimeException("Unreachable code during Isabelle instance creation");
        }
    }

    /**
     * Starts an Isabelle instance using the Isabelle installation location provided by the user in
     * the settings.
     *
     * @return freshly started Isabelle instance
     * @throws IsabelleNotFoundException if Isabelle could not be found at the location stored in
     *         the settings
     */
    private Isabelle startIsabelleInstance() throws IsabelleNotFoundException {
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
            throw new IsabelleNotFoundException(
                "Can't find Isabelle at " + settings.getIsabellePath());
        }
        return isabelle;
    }

    /**
     * Creates a theory object for use in solvers.
     * <p>
     * Requires the translation theories to be present.
     *
     * @param isabelle The Isabelle instance, which creates the theory object
     * @param settings Isabelle settings, which show the location of the translation theories
     * @return Theory object matching the given isabelle instance
     */
    private static Theory beginTheory(Isabelle isabelle, IsabelleTranslationSettings settings) {
        MLFunction3<Path, TheoryHeader, List<Theory>, Theory> begin_theory =
            MLValue.compileFunction(
                "fn (path, header, parents) => Resources.begin_theory path header parents",
                isabelle,
                Implicits.pathConverter(), Implicits.theoryHeaderConverter(),
                new ListConverter<>(Implicits.theoryConverter()), Implicits.theoryConverter());
        MLFunction2<String, Position, TheoryHeader> header_read =
            MLValue.compileFunction("fn (text,pos) => Thy_Header.read pos text", isabelle,
                de.unruh.isabelle.mlvalue.Implicits.stringConverter(),
                Implicits.positionConverter(), Implicits.theoryHeaderConverter());


        TheoryHeader header = header_read
                .apply(settings.getHeader(), Position.none(isabelle), isabelle,
                    de.unruh.isabelle.mlvalue.Implicits.stringConverter(),
                    Implicits.positionConverter())
                .retrieveNow(Implicits.theoryHeaderConverter(), isabelle);
        Path topDir = settings.getTranslationPath();


        return begin_theory.apply(topDir, header,
            header.imports(isabelle).map((String name) -> Theory.apply(name, isabelle)), isabelle,
            Implicits.pathConverter(), Implicits.theoryHeaderConverter(),
            new ListConverter<>(Implicits.theoryConverter()))
                .retrieveNow(Implicits.theoryConverter(), isabelle);
    }

    /**
     * A record bundling a given instance to a theory. This is necessary as a theory object is only
     * usable in conjunction with the instance used to create it.
     *
     * @param instance the instance
     * @param theory the theory
     */
    private record IsabelleResourceImpl(Isabelle instance, Theory theory)
            implements IsabelleResource {

        @Override
        public boolean isDestroyed() {
            return instance.isDestroyed();
        }

        @Override
        public void destroy() {
            instance.destroy();
        }

        private void interruptIntern() throws IsabelleMLException {
            instance.executeMLCodeNow("error \"Interrupt\"");
        }

        @Override
        public void interrupt() {
            try {
                interruptIntern();
            } catch (IsabelleMLException e) {
                // Always throws this due to the way Isabelle is interrupted.
            }
        }
    }
}
