/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core.fx;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.EventObject;
import java.util.List;
import java.util.function.Consumer;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Headless (toolkit-free) unit test of the WP-1 mediator seams of {@link KeYMediatorF} — the
 * port of the Swing {@code de.uka.ilkd.key.core.KeYMediator} surfaces the extension ports and
 * the exit flow were missing:
 * <ul>
 * <li>the opened-proofs accessor ({@link KeYMediatorF#getCurrentlyOpenedProofs()} — Swing
 * KeYMediator.java:800-808),</li>
 * <li>the extension-object register/lookup registry ({@link KeYMediatorF#register(Object,
 * Class)} / {@link KeYMediatorF#lookup(Class)} — Swing KeYMediator.java:589-626),</li>
 * <li>the GUI-listener registry and the shutdown event ({@link KeYMediatorF#addGUIListener}
 * / {@link KeYMediatorF#fireShutDown(EventObject)} — Swing KeYMediator.java:306-410, the
 * {@code GUIListener.shutDown} the exit flow fires),</li>
 * <li>the proof-load listener registry ({@link KeYMediatorF#registerProofLoadListener} /
 * {@link KeYMediatorF#fireProofLoaded(Proof)} — Swing KeYMediator.java:124-134, :413-421),</li>
 * <li>the auto-mode context API for foreign proofs ({@link KeYMediatorF#initiateAutoMode} /
 * {@link KeYMediatorF#finishAutoMode} — Swing KeYMediator.java:535-566).</li>
 * </ul>
 * <p>
 * Like {@code SequentMenuModelFTest} the tests run against a real proof of the standard JavaDL
 * profile loaded headlessly via {@link KeYEnvironment}; the tests deliberately avoid the FX
 * toolkit (no controls, no {@code Platform} calls) — the observable auto-mode property is
 * published directly when no toolkit is running (see
 * {@code KeYMediatorF.publishAutoModeRunning}).
 */
class KeYMediatorFSeamsTest {

    private KeYEnvironment<?> env;
    private Proof proof;
    private KeYMediatorF mediator;

    @BeforeEach
    void loadProof() throws Exception {
        Path dir = Files.createTempDirectory("mediator-seams");
        Path main = dir.resolve("test.key");
        // No \include: the JavaDL profile loads the standard library from the classpath.
        Files.writeString(main, "\\problem { true }\n");
        env = KeYEnvironment.load(main);
        proof = env.getLoadedProof();
        mediator = new KeYMediatorF();
    }

    @AfterEach
    void unloadProof() {
        if (env != null) {
            env.dispose();
        }
    }

    /** A service interface for the registry round trips (the Swing {@code Lookup} shape). */
    interface SeamService {
        String id();
    }

    /** A second service interface for the registry round trips. */
    interface OtherSeamService {
    }

    private static final class SeamServiceImpl implements SeamService {
        @Override
        public String id() {
            return "one";
        }
    }

    private static final class OtherSeamServiceImpl implements OtherSeamService {
    }

    // ---------------------------------------------------------------------------------
    // opened-proofs accessor: the live mutable list (Swing TaskTree adds, ProofTreeView
    // removes directly through the accessor)
    // ---------------------------------------------------------------------------------

    @Test
    void currentlyOpenedProofsIsLiveAndMutable() {
        assertTrue(mediator.getCurrentlyOpenedProofs().isEmpty(),
            "no proof is registered on a fresh mediator");
        List<Proof> opened = mediator.getCurrentlyOpenedProofs();
        opened.add(proof);
        assertEquals(1, mediator.getCurrentlyOpenedProofs().size(),
            "the accessor must expose the live list (Swing TaskTree.addProof, TaskTree.java:117)");
        opened.remove(proof);
        assertTrue(mediator.getCurrentlyOpenedProofs().isEmpty(),
            "removal through the accessor must be visible (Swing ProofTreeView, :726)");
    }

    // ---------------------------------------------------------------------------------
    // extension-object registry: register / lookup / deregister (Swing KeYMediator.java
    // :589-626, the exploration port registers its model this way)
    // ---------------------------------------------------------------------------------

    @Test
    void registryRegisterLookupDeregisterRoundTrip() {
        SeamServiceImpl impl = new SeamServiceImpl();
        assertNull(mediator.lookup(SeamService.class),
            "nothing is registered for the service");
        mediator.register(impl, SeamService.class);
        assertSame(impl, mediator.lookup(SeamService.class),
            "lookup must return the registered implementation");
        mediator.deregister(impl, SeamService.class);
        assertNull(mediator.lookup(SeamService.class),
            "after the deregistration the lookup must be empty again");
    }

    @Test
    void registryLookupIsPerServiceClass() {
        SeamServiceImpl one = new SeamServiceImpl();
        OtherSeamServiceImpl other = new OtherSeamServiceImpl();
        mediator.register(one, SeamService.class);
        mediator.register(other, OtherSeamService.class);
        SeamService lookedUp = mediator.lookup(SeamService.class);
        assertNotNull(lookedUp, "the service must be look-up-able");
        assertSame(one, lookedUp,
            "the most recently registered implementation is the default (Lookup.register)");
        OtherSeamService lookedUpOther = mediator.lookup(OtherSeamService.class);
        assertNotNull(lookedUpOther, "the lookup must be keyed by the service class");
        assertSame(other, lookedUpOther, "the two services must be independent namespaces");
    }

    @Test
    void registryDeregisterForeignObjectIsNoOp() {
        SeamServiceImpl impl = new SeamServiceImpl();
        mediator.register(impl, SeamService.class);
        mediator.deregister(new SeamServiceImpl(), SeamService.class);
        SeamService lookedUp = mediator.lookup(SeamService.class);
        assertNotNull(lookedUp);
        assertSame(impl, lookedUp,
            "deregistering a not-registered object must not clear the service");
    }

    // ---------------------------------------------------------------------------------
    // GUI-listener registry + fireShutDown (Swing KeYMediator.java:306-410)
    // ---------------------------------------------------------------------------------

    /** Records which of the three GUI events arrived, in order. */
    private static final class RecordingGUIListener implements GUIListenerF {
        final List<String> events = new ArrayList<>();

        @Override
        public void modalDialogOpened(EventObject e) {
            events.add("modalDialogOpened");
        }

        @Override
        public void modalDialogClosed(EventObject e) {
            events.add("modalDialogClosed");
        }

        @Override
        public void shutDown(EventObject e) {
            events.add("shutDown:" + e.getSource());
        }
    }

    @Test
    void guiListenersReceiveTheThreeEvents() {
        RecordingGUIListener listener = new RecordingGUIListener();
        mediator.addGUIListener(listener);

        Object source = new Object();
        mediator.requestModalAccess(source);
        mediator.freeModalAccess(source);
        mediator.fireShutDown(new EventObject(source));

        assertEquals(List.of("modalDialogOpened", "modalDialogClosed", "shutDown:" + source),
            listener.events, "all three GUI events must be delivered in order");

        mediator.removeGUIListener(listener);
        mediator.fireShutDown(new EventObject(source));
        assertEquals(3, listener.events.size(),
            "after removeGUIListener no further event may be delivered");
    }

    @Test
    void fireShutDownWithoutListenersIsNoOp() {
        // Swing fires the shutdown event unconditionally in the exit flow
        // (ExitMainAction.java:83) even when no listener is registered
        mediator.fireShutDown(new EventObject(this));
    }

    // ---------------------------------------------------------------------------------
    // proof-load listener registry (Swing KeYMediator.java:124-134, :413-421)
    // ---------------------------------------------------------------------------------

    @Test
    void proofLoadListenersReceiveTheFiredProof() {
        List<Proof> fired = new ArrayList<>();
        Consumer<Proof> listener = fired::add;
        mediator.registerProofLoadListener(listener);

        mediator.fireProofLoaded(proof);
        mediator.fireProofLoaded(proof); // a listener MUST accept the same proof twice

        assertEquals(2, fired.size(), "every fire must be delivered");
        assertSame(proof, fired.get(0), "the loaded proof must be delivered");
    }

    @Test
    void fireProofLoadedIgnoresNull() {
        List<Proof> fired = new ArrayList<>();
        mediator.registerProofLoadListener(fired::add);
        mediator.fireProofLoaded(null);
        assertTrue(fired.isEmpty(), "a null proof is ignored (Swing fireProofLoaded)");
    }

    // ---------------------------------------------------------------------------------
    // auto-mode context API for foreign proofs (Swing KeYMediator.java:535-566)
    // ---------------------------------------------------------------------------------

    @Test
    void autoModeContextForForeignProofTracksTheState() {
        assertFalse(mediator.isInAutoMode(), "no auto mode on a fresh mediator");
        assertFalse(mediator.autoModeRunningProperty().get());

        // the proof is handed to the context API explicitly — the API works on the given proof
        // regardless of the selection (Swing initiateAutoMode/finishAutoMode, the caching port
        // invokes it on the referenced, non-selected proof). The proof is selected here as
        // well, so finishAutoMode's default selection has a proof to work on.
        mediator.getSelectionModel().setSelectedProof(proof);

        mediator.initiateAutoMode(proof, true, false);
        assertTrue(mediator.isInAutoMode(),
            "initiateAutoMode(fullStop=true) must mark the auto mode active");
        assertTrue(mediator.autoModeRunningProperty().get(),
            "the observable property must be published (the FX UI freeze/disable channel)");

        mediator.finishAutoMode(proof, true, true, null);
        assertFalse(mediator.isInAutoMode(),
            "finishAutoMode(fullStop=true) must clear the auto mode state");
        assertFalse(mediator.autoModeRunningProperty().get(),
            "the observable property must be unpublished after the run");
    }

    @Test
    void autoModeContextWithoutFullStopDoesNotTouchTheState() {
        mediator.getSelectionModel().setSelectedProof(proof);
        mediator.initiateAutoMode(proof, false, false);
        assertFalse(mediator.isInAutoMode(),
            "initiateAutoMode(fullStop=false) must not set the auto mode flag (Swing "
                + "stopInterface sets inAutoMode only for a full stop)");
        mediator.finishAutoMode(proof, false, true, null);
        assertFalse(mediator.isInAutoMode(),
            "finishAutoMode(fullStop=false) must not clear an untouched state");
    }

    @Test
    void autoModeContextRunsTheCustomSelection() {
        mediator.getSelectionModel().setSelectedProof(proof);
        List<Proof> selections = new ArrayList<>();
        mediator.finishAutoMode(proof, true, true, () -> selections.add(proof));
        assertEquals(1, selections.size(),
            "finishAutoMode must run the given selection instead of the default selection");
    }

    @Test
    void autoModeContextDefaultSelectionSelectsTheLoadedProof() {
        mediator.getSelectionModel().setSelectedProof(proof);
        mediator.finishAutoMode(proof, true, true, null);
        assertSame(proof, mediator.getSelectedProof(),
            "finishAutoMode(selection=null) must perform the default selection");
    }
}
