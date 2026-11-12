/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.core.fx;

import java.util.EventObject;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.Consumer;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.beans.property.ReadOnlyBooleanWrapper;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.fx.UserActionListenerF;
import de.uka.ilkd.key.gui.fx.actions.useractions.UserActionF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.rule.OneStepSimplifier;

import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.javafx.FxUtil;
import org.key_project.util.lookup.Lookup;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The mediator of the JavaFX user interface, counter-part of {@code de.uka.ilkd.key.core.
 * KeYMediator} in the Swing module {@code key.ui}.
 * <p>
 * <b>Milestone M2, skeleton.</b> The mediator owns the {@link KeYSelectionModel} (it is the
 * model's {@link KeYSelectionModel.ProofBinder}: {@link #setProof(Proof, Proof)} is called
 * whenever the selected proof changes) and shares the {@link NotationInfo} of the displayed
 * proof: {@link #setProof(Proof, Proof)} swaps the proof listeners, rebinds the proof's
 * abbreviation map into the notation info and refreshes the one-step simplifier — exactly like
 * the Swing mediator. Interactive rule applications re-default the selection
 * ({@link #defaultSelection()}) so the attached views update; during auto mode the events are
 * suspended by the core ({@code Proof#suspendNonEssentialListeners}) and the views refresh from
 * the final state on {@code autoModeStopped}.
 * <p>
 * Deliberately deferred: notifications ({@code ProofClosedNotificationEvent} needs the Swing
 * notification events of key.ui — the FX notification arrives with M3), user
 * action listeners and the task/progress plumbing of the Swing mediator. The auto saver is
 * wired since MP7 ({@link #setAutoSave(int)} / {@link #getAutoSaver()}, mirroring the Swing
 * mediator).
 */
public final class KeYMediatorF implements KeYSelectionModel.ProofBinder {

    private static final Logger LOGGER = LoggerFactory.getLogger(KeYMediatorF.class);

    /** the notation info shared by all views printing terms/sequents (abbreviations, unicode). */
    private final NotationInfo notationInfo = new NotationInfo();

    /** the selection model, {@link #setProof(Proof, Proof)} is bound as its {@link ProofBinder}. */
    private final KeYSelectionModel keySelectionModel = new KeYSelectionModel(this);

    private final ProofTreeListener proofTreeListener = new MediatorProofTreeListener();

    private final RuleAppListenerProofListener proofListener = new RuleAppListenerProofListener();

    /** number of goals closed by the last auto mode run (for the status line in M3). */
    private int goalsClosedByAutoMode;

    /** whether an auto mode run is currently active (tracked via {@link #proofListener}). */
    private volatile boolean inAutoMode;

    /** the proof control this mediator is attached to, may be {@code null} until M3. */
    private ProofControl proofControl;

    /**
     * menu: MP7 — the optional {@link AutoSaver} (Swing {@code KeYMediator} field,
     * KeYMediator.java:85-87); armed/disarmed via {@link #setAutoSave(int)}, the saver follows
     * the selected proof through {@link #setProof(Proof, Proof)}.
     */
    private AutoSaver autoSaver;

    // ------------------------------------------------------------------
    // WP-1 — the mediator seams of the Swing KeYMediator that the FX extension ports and
    // the exit flow were missing (see KNOWN-SIMPLIFIED.md: caching CachingExtensionF.java:778,
    // exploration ExplorationExtensionF.java:280, slicing SlicingExtensionF.java:49,
    // MainWindowF.java:3721). Swing sources: de.uka.ilkd.key.core.KeYMediator.
    // ------------------------------------------------------------------

    /**
     * WP-1 — the currently opened proofs (Swing {@code KeYMediator.currentlyOpenedProofs},
     * KeYMediator.java:92-96, accessor :800-808): a live mutable list — Swing's {@code
     * TaskTree.addProof} adds every registered proof (TaskTree.java:117) and
     * {@code ProofTreeView} removes the disposed ones (ProofTreeView.java:726). In the FX UI the
     * {@code ProofManagerF} multi-proof state is the single registration point; {@code
     * MainWindowF} mirrors it into this list.
     */
    private final List<Proof> currentlyOpenedProofs = new CopyOnWriteArrayList<>();

    /**
     * WP-1 — registered proof load listeners (Swing {@code KeYMediator.proofLoadListeners},
     * KeYMediator.java:99-104): called whenever a new proof is loaded, but before it is
     * replayed, via {@link #fireProofLoaded(Proof)} (Swing
     * {@code WindowUserInterfaceControl.registerProofAggregate}, WindowUserInterfaceControl.java
     * :519-525). A listener MUST be able to accept the same proof twice.
     */
    private final List<Consumer<Proof>> proofLoadListeners = new CopyOnWriteArrayList<>();

    /**
     * WP-1 — the registered GUI listeners (Swing {@code KeYMediator.listenerList},
     * KeYMediator.java:60).
     */
    private final List<GUIListenerF> guiListeners = new CopyOnWriteArrayList<>();

    /**
     * WP-7 — the registered user-action listeners (Swing {@code KeYMediator
     * .userActionListeners}, KeYMediator.java:815-825).
     */
    private final List<UserActionListenerF> userActionListeners = new CopyOnWriteArrayList<>();

    /**
     * WP-1 — user-defined data / extension-object registry (Swing
     * {@code KeYMediator.userData}, KeYMediator.java:585).
     */
    private @Nullable Lookup userData;


    /**
     * Observable auto mode state for the UI (buttons and menu items bind their enabled state to
     * it); updated on the FX thread from the auto mode events.
     */
    private final ReadOnlyBooleanWrapper autoModeRunning =
        new ReadOnlyBooleanWrapper(this, "autoModeRunning");

    /**
     * Creates the mediator. The selection model is owned by the mediator; views and the main
     * window obtain it via {@link #getSelectionModel()}.
     */
    public KeYMediatorF() {
    }

    /**
     * Registers the mediator's auto mode listener on the given proof control (the Swing ctor does
     * this with {@code ui.getProofControl()}). Without attachment the mediator still works, but
     * {@link #isInAutoMode()} stays {@code false}.
     *
     * @param control the proof control of the application
     */
    public void attach(ProofControl control) {
        this.proofControl = control;
        control.addAutoModeListener(proofListener);
    }

    /**
     * {@inheritDoc}
     * <p>
     * Swaps the mediator's proof listeners to the new proof, rebinds the proof's abbreviation map
     * into the shared {@link #getNotationInfo() notation info} and refreshes the one-step
     * simplifier (Swing {@code KeYMediator#setProof}).
     */
    @Override
    public void setProof(Proof newProof, Proof previousProof) {
        if (previousProof == newProof) {
            return;
        }
        LOGGER.debug("Mediator binding proof: {} -> {}",
            previousProof == null ? null : previousProof.name(),
            newProof == null ? null : newProof.name());
        if (previousProof != null) {
            previousProof.removeProofTreeListener(proofTreeListener);
            previousProof.removeRuleAppListener(proofListener);
        }
        if (newProof != null) {
            notationInfo.setAbbrevMap(newProof.abbreviations());
            newProof.addProofTreeListener(proofTreeListener);
            newProof.addRuleAppListener(proofListener);
        }
        // menu: MP7 — the auto saver follows the selected proof (Swing
        // {@code KeYMediator.setProof}, KeYMediator.java:240-241: {@code
        // getAutoSaver().setProof(newProof)}); the saver accepts {@code null} (abandoned proof)
        if (getAutoSaver() != null) {
            getAutoSaver().setProof(newProof);
        }
        OneStepSimplifier.refreshOSS(newProof);
    }

    /**
     * menu: MP7 — arms or disarms the {@link AutoSaver} (Swing {@code KeYMediator.setAutoSave},
     * KeYMediator.java:148-150: {@code autoSaver = interval > 0 ? new AutoSaver(interval, true)
     * : null}); the saver writes intermediate .key artifacts every {@code interval} proof steps
     * and the final closed proof (see {@link AutoSaver}).
     *
     * @param interval the save interval in proof steps, 0 disables auto save
     */
    public void setAutoSave(int interval) {
        autoSaver = interval > 0 ? new AutoSaver(interval, true) : null;
    }

    /**
     * @return the auto saver to use, or {@code null} if auto save is disabled (Swing
     *         {@code KeYMediator.getAutoSaver}, KeYMediator.java:791-796)
     */
    public AutoSaver getAutoSaver() {
        return autoSaver;
    }

    /**
     * @return the selection model of the mediator
     */
    public KeYSelectionModel getSelectionModel() {
        return keySelectionModel;
    }

    /**
     * @return the notation info shared by the views (abbreviation map follows the selected proof)
     */
    public NotationInfo getNotationInfo() {
        return notationInfo;
    }

    /**
     * @return the currently selected proof or {@code null}
     */
    public Proof getSelectedProof() {
        return keySelectionModel.getSelectedProof();
    }

    /**
     * uicontrol (P2b): whether a proof is loaded (port of Swing
     * {@code KeYMediator.ensureProofLoaded}, KeYMediator.java:152-154); used by the source
     * consistency toggle and other actions that need a loaded proof before taking effect.
     *
     * @return {@code true} if a proof is selected
     */
    public boolean ensureProofLoaded() {
        return getSelectedProof() != null;
    }

    /**
     * @return the currently selected node or {@code null}
     */
    public Node getSelectedNode() {
        return keySelectionModel.getSelectedNode();
    }

    /**
     * @return the currently selected goal or {@code null}
     */
    public Goal getSelectedGoal() {
        return keySelectionModel.getSelectedGoal();
    }

    /**
     * @return the services of the selected proof or {@code null}
     */
    public Services getServices() {
        Proof selectedProof = getSelectedProof();
        return selectedProof != null ? selectedProof.getServices() : null;
    }

    /**
     * Selects the default node/goal of the selected proof (first open goal or a leaf) and fires
     * {@code selectedNodeChanged}.
     */
    public void defaultSelection() {
        keySelectionModel.defaultSelection();
    }

    /**
     * @return {@code true} if an auto mode run is currently active
     */
    public boolean isInAutoMode() {
        return inAutoMode;
    }

    /**
     * @return the observable auto mode state (updated on the FX thread); the automatic proof
     *         buttons and menu items bind their disabled state to it
     */
    public ReadOnlyBooleanProperty autoModeRunningProperty() {
        return autoModeRunning.getReadOnlyProperty();
    }

    /**
     * Starts the automatic prover on the selected proof (Swing {@code AutoModeAction}: guarded by
     * {@code isInAutoMode} and {@code ProofControl#isAutoModeSupported}, then
     * {@code startAutoMode(proof, proof.openEnabledGoals())}). No-op without an attached proof
     * control, without a selected proof, while a run is active or when auto mode is not supported
     * for the proof.
     */
    public void startAutoMode() {
        Proof proof = getSelectedProof();
        if (proofControl == null || proof == null || inAutoMode
                || !proofControl.isAutoModeSupported(proof)) {
            return;
        }
        proofControl.startAutoMode(proof, proof.openEnabledGoals());
    }

    /** Stops the running automatic prover (Swing {@code AutoModeAction}); no-op when idle. */
    public void stopAutoMode() {
        if (proofControl != null && inAutoMode) {
            proofControl.stopAutoMode();
        }
    }

    // ------------------------------------------------------------------
    // WP-1 — auto-mode context API for foreign proofs (Swing
    // KeYMediator.initiateAutoMode/finishAutoMode, KeYMediator.java:535-566). Swing's caching
    // port wraps the CopyReferenceResolver copy into these (CachingExtension.java:312-319);
    // the FX port of CopyBeforeDispose needs the same seam for a proof that is not the
    // selected one.
    // ------------------------------------------------------------------

    /**
     * WP-1 — performs the standard preparations for starting an auto mode run on the given
     * (possibly foreign) proof (Swing {@code KeYMediator.initiateAutoMode},
     * KeYMediator.java:535-540): freezes the interface and marks the auto mode active
     * ({@code fullStop}), flips the rule app index to the requested mode.
     * <p>
     * Swing {@code stopInterface(fullStop)} disables the UI via
     * {@code ui.notifyAutoModeBeingStarted()} and sets {@code inAutoMode}; in the FX UI both the
     * freeze ({@code MainWindowF}'s listener on the observable property) and the enabled state
     * of every proof action are bound to {@link #autoModeRunningProperty()}, so publishing the
     * property is the FX-side interface stop. Swing additionally fires
     * {@code getUI().getProofControl().fireAutoModeStarted(...)} — the Swing-only method of
     * {@code KeYMediatorProofControl}; the core {@code AbstractProofControl.fireAutoModeStarted}
     * is protected and not reachable from the mediator, so the observable property is the FX
     * notification channel.
     *
     * @param proof the {@link Proof} to be worked on (may differ from the selected proof)
     * @param fullStop if a full freeze of the interface is requested
     * @param interactive whether the needed taclet index is for interactive or automatic use
     *        (normally {@code false})
     */
    public void initiateAutoMode(Proof proof, boolean fullStop, boolean interactive) {
        if (fullStop) {
            inAutoMode = true;
            publishAutoModeRunning(true);
        }
        setInteractive(interactive);
    }

    /**
     * WP-1 — performs the standard preparations for finishing an auto mode run on the given
     * (possibly foreign) proof (Swing {@code KeYMediator.finishAutoMode}, KeYMediator.java
     * :550-566): flips the rule app index back, unfreezes the interface ({@code fullStop}) and
     * selects a node/proof by running the given selector (the default selection when
     * {@code selection} is {@code null}).
     *
     * @param proof the {@link Proof} that was worked on
     * @param fullStop if a full unfreeze of the interface is requested
     * @param interactive whether the needed taclet index is for interactive or automatic use
     *        (normally {@code true})
     * @param selection a runnable that selects the correct node after unfreezing the interface,
     *        may be {@code null}
     */
    public void finishAutoMode(Proof proof, boolean fullStop, boolean interactive,
            @Nullable Runnable selection) {
        setInteractive(interactive);
        if (fullStop) {
            inAutoMode = false;
            publishAutoModeRunning(false);
        }
        if (selection == null) {
            keySelectionModel.defaultSelection();
        } else {
            selection.run();
        }
    }

    /**
     * Swing {@code KeYMediator.setInteractive} (KeYMediator.java:476-484): switches the rule
     * app index of the selected proof between interactive and automatic use.
     *
     * @param b {@code true} to switch to interactive mode
     */
    public void setInteractive(boolean b) {
        Proof selectedProof = getSelectedProof();
        if (selectedProof != null) {
            if (b) {
                selectedProof.setRuleAppIndexToInteractiveMode();
            } else {
                selectedProof.setRuleAppIndexToAutoMode();
            }
        }
    }

    /**
     * WP-1 — publishes the auto-mode state on the observable property, marshalled to the FX
     * thread (auto-mode events may originate from the prover thread — Swing's
     * {@code stopInterface}/{@code startInterface} marshal via {@code ThreadUtilities}).
     * <p>
     * In a toolkit-free environment (the headless seam tests) {@code Platform.runLater} fails
     * with an {@link IllegalStateException}; there the state is published directly, because no
     * UI listeners are attached in that environment.
     */
    private void publishAutoModeRunning(boolean running) {
        try {
            FxUtil.runLater(() -> autoModeRunning.set(running));
        } catch (IllegalStateException toolkitNotInitialized) {
            LOGGER.debug("No JavaFX toolkit: publishing the auto-mode state directly");
            autoModeRunning.set(running);
        }
    }

    // ------------------------------------------------------------------
    // WP-1 — opened-proofs accessor, extension-object registry, GUI-listener and proof-load
    // listener registries (Swing KeYMediator.java:129-134, 300-320, 403-421, 585-626,
    // 800-808).
    // ------------------------------------------------------------------

    /**
     * WP-1 — provides the list of currently opened proofs (Swing
     * {@code KeYMediator.getCurrentlyOpenedProofs}, KeYMediator.java:800-808): the live list can
     * be used directly inside components (Swing {@code TaskTree} adds, {@code ProofTreeView}
     * removes).
     *
     * @return the live, mutable list of opened proofs
     */
    public List<Proof> getCurrentlyOpenedProofs() {
        return currentlyOpenedProofs;
    }

    /**
     * WP-1 — registers a proof load listener (Swing
     * {@code KeYMediator.registerProofLoadListener}, KeYMediator.java:124-134): called whenever
     * a new proof is loaded, but before it is replayed. The listener MUST be able to accept the
     * same proof twice.
     *
     * @param listener the callback
     */
    public void registerProofLoadListener(Consumer<Proof> listener) {
        proofLoadListeners.add(listener);
    }

    /**
     * WP-1 — fires the proof-loaded event (Swing {@code KeYMediator.fireProofLoaded},
     * KeYMediator.java:413-421): delivered to every registered proof load listener.
     *
     * @param p the proof that was just loaded and is about to be replayed ({@code null} is
     *        ignored, like in Swing)
     */
    public void fireProofLoaded(Proof p) {
        if (p == null) {
            return;
        }
        for (Consumer<Proof> listener : proofLoadListeners) {
            listener.accept(p);
        }
    }

    /**
     * WP-1 — adds a listener to GUI events (Swing {@code KeYMediator.addGUIListener},
     * KeYMediator.java:306-309).
     *
     * @param listener the {@link GUIListenerF} to be added
     */
    public void addGUIListener(GUIListenerF listener) {
        guiListeners.add(listener);
    }

    /**
     * WP-1 — removes a listener from GUI events (Swing
     * {@code KeYMediator.removeGUIListener}, KeYMediator.java:315-318).
     *
     * @param listener the {@link GUIListenerF} to be removed
     */
    public void removeGUIListener(GUIListenerF listener) {
        guiListeners.remove(listener);
    }

    /**
     * WP-7 — adds another listener for user actions (Swing
     * {@code KeYMediator.addUserActionListener}, KeYMediator.java:815-818).
     *
     * @param listener the {@link UserActionListenerF} to be added
     */
    public void addUserActionListener(UserActionListenerF listener) {
        userActionListeners.add(listener);
    }

    /**
     * WP-7 — notifies all user action listeners about a performed action (Swing
     * {@code KeYMediator.fireActionPerformed}, KeYMediator.java:824-827).
     *
     * @param action the user action
     */
    public void fireActionPerformed(UserActionF action) {
        for (UserActionListenerF listener : userActionListeners) {
            listener.actionPerformed(action);
        }
    }

    /**
     * WP-1 — fires the request of a GUI component for modal access (Swing
     * {@code KeYMediator.requestModalAccess}, KeYMediator.java:352-356); can be used to disable
     * all views even if the GUI component has no built-in modal support.
     *
     * @param src the object asking for modal access
     */
    public void requestModalAccess(Object src) {
        fireModalDialogOpened(new EventObject(src));
    }

    /**
     * WP-1 — frees the modal access requested with {@link #requestModalAccess(Object)} (Swing
     * {@code KeYMediator.freeModalAccess}, KeYMediator.java:359-363).
     *
     * @param src the object that requested modal access
     */
    public void freeModalAccess(Object src) {
        fireModalDialogClosed(new EventObject(src));
    }

    /**
     * WP-1 — fires that a GUI component asked for modal access (Swing
     * {@code KeYMediator.fireModalDialogOpened}, KeYMediator.java:366-377).
     *
     * @param e the event
     */
    public void fireModalDialogOpened(EventObject e) {
        for (GUIListenerF listener : guiListeners) {
            listener.modalDialogOpened(e);
        }
    }

    /**
     * WP-1 — fires that the GUI component holding modal access has been closed, so views can be
     * enabled again (Swing {@code KeYMediator.fireModalDialogClosed}, KeYMediator.java:382-393).
     *
     * @param e the event
     */
    public void fireModalDialogClosed(EventObject e) {
        for (GUIListenerF listener : guiListeners) {
            listener.modalDialogClosed(e);
        }
    }

    /**
     * WP-1 — fires the shut-down event (Swing {@code KeYMediator.fireShutDown},
     * KeYMediator.java:400-410): the exit flow of the main window calls this so the
     * {@link GUIListenerF}s perform their shutdown side effects (Swing
     * {@code MainGUIListener.shutDown}, MainWindow.java:1855-1858).
     *
     * @param e the event
     */
    public void fireShutDown(EventObject e) {
        for (GUIListenerF listener : guiListeners) {
            listener.shutDown(e);
        }
    }

    /**
     * WP-1 — retrieves user-defined data (Swing {@code KeYMediator.lookup},
     * KeYMediator.java:589-604): the first registered implementation of the service class, or
     * {@code null} when none is registered (Swing swallows the {@link IllegalStateException} of
     * the lookup in the same way).
     *
     * @param service the class for which the data were registered
     * @param <T> any class
     * @return the registered implementation or {@code null}
     * @see #register(Object, Class)
     */
    public <T> @Nullable T lookup(Class<T> service) {
        try {
            if (userData == null) {
                return null;
            }
            return userData.get(service);
        } catch (IllegalStateException ignored) {
            return null;
        }
    }

    /**
     * WP-1 — registers a user-defined data / extension object (Swing
     * {@code KeYMediator.register}, KeYMediator.java:606-610; the Swing exploration port
     * registers its model with {@code mediator.register(model, ExplorationModeModel.class)},
     * ExplorationExtension.java:103).
     *
     * @param obj the object to register
     * @param service the class under which it is registered
     * @param <T> the service type
     */
    public <T> void register(T obj, Class<T> service) {
        getUserData().register(obj, service);
    }

    /**
     * WP-1 — removes a previously registered user-defined data (Swing
     * {@code KeYMediator.deregister}, KeYMediator.java:612-622).
     *
     * @param obj the registered object
     * @param service the class under which the data was registered
     * @param <T> the service type
     */
    public <T> void deregister(T obj, Class<T> service) {
        if (userData != null) {
            userData.deregister(obj, service);
        }
    }

    /**
     * WP-1 — the associated lookup of user-defined data (Swing
     * {@code KeYMediator.getUserData}, KeYMediator.java:625-631).
     *
     * @return the (lazily created) lookup
     */
    public Lookup getUserData() {
        if (userData == null) {
            userData = new Lookup();
        }
        return userData;
    }

    /**
     * prooftree (P3a, C23): starts the automatic prover restricted to the given goals (Swing
     * {@code RunStrategyOnNodeUserAction.apply} — the "Apply Strategy" popup item of the proof
     * tree): all enabled goals below the invoked node, or the invoked node itself when it is an
     * open goal. No-op without an attached proof control or while a run is active.
     *
     * @param goals the goals to run on, may be empty (then nothing is started)
     */
    public void startAutoMode(ImmutableList<Goal> goals) {
        Proof proof = getSelectedProof();
        if (proofControl == null || proof == null || inAutoMode
                || !proofControl.isAutoModeSupported(proof) || goals == null || goals.isEmpty()) {
            return;
        }
        proofControl.startAutoMode(proof, goals);
    }

    /**
     * prooftree (P3a, C23): prunes the proof below the given node and selects it (Swing
     * {@code KeYMediator.setBack(Node)} — the "Prune Proof" popup item of the proof tree).
     *
     * @param node the cutting point, must belong to the selected proof
     */
    public void pruneNode(Node node) {
        if (node != null) {
            setBack(node);
        }
    }

    /**
     * Undoes the last rule application on the selected goal (Swing {@code GoalBackAction}):
     * without a selected goal the newest goal of the selected node's subtree is used — the one
     * with the highest node serial number, where a closed goal wins if its serial is higher. As
     * in Swing, {@code Proof.pruneProof} refuses to prune a closed cutting point while
     * {@code GeneralSettings.noPruningClosed} is set (the default), so a goal back on a closed
     * branch is a no-op.
     */
    public void goalBack() {
        Node selNode = getSelectedNode();
        Goal selGoal = getSelectedGoal();
        if (selGoal == null && selNode != null) {
            selGoal = findNewestGoal(selNode);
        }
        if (selGoal != null) {
            setBack(selGoal);
            // set the selection to give the user a visual feedback (Swing GoalBackAction);
            // selGoal.node() is re-read after the prune, see setBack(Goal)
            keySelectionModel.setSelectedNode(selGoal.node());
        }
    }

    /**
     * Removes the proof subtree below the selected node (Swing {@code PruneProofAction}).
     */
    public void pruneProof() {
        Node node = getSelectedNode();
        if (node != null) {
            setBack(node);
        }
    }

    /**
     * Swing {@code KeYMediator.setBack(Goal)}: undoes the rule application that created the goal
     * ({@code ProofControl.pruneTo(Goal)} prunes to the goal's parent) and selects the pre-rule
     * node. The Swing task-finished notification is not yet mirrored.
     */
    private void setBack(Goal goal) {
        Proof proof = getSelectedProof();
        if (proof == null) {
            return;
        }
        if (goal.node().parent() != null) {
            // ProofControl.pruneTo(Goal): undo the rule application that created the goal's node
            proof.pruneProof(goal.node().parent());
        }
        // The goal's node must be re-read here: the pruner re-associates the goal with the
        // cutting point (Goal.pruneToParent), the old node is detached and its parent pointer
        // is cleared (Node.remove). Swing's KeYMediator.setBack reads goal.node() after
        // pruneTo as well.
        Node node = goal.node();
        keySelectionModel.setSelectedNode(node == proof.root() ? node : node.parent());
    }

    /**
     * Swing {@code KeYMediator.setBack(Node)}: prunes the subtree below the given node and
     * selects it.
     */
    private void setBack(Node node) {
        node.proof().pruneProof(node);
        keySelectionModel.setSelectedNode(node);
    }

    /**
     * P3b/B11: the display name of the rule that the next "Goal Back" would undo, or {@code null}
     * when there is none (Swing {@code GoalBackAction.updateName},
     * GoalBackAction.java:113-125: the name of the {@code getAppliedRuleApp} of the parent of the
     * newest goal's node is appended to the menu item text).
     *
     * @return the rule display name (e.g. {@code "andLeft"}), or {@code null} when no goal / no
     *         applied rule is found
     */
    public @Nullable String goalBackRuleName() {
        Goal goal = findNewestGoal(getSelectedNode());
        if (goal != null && goal.node() != null && goal.node().parent() != null) {
            RuleApp app = goal.node().parent().getAppliedRuleApp();
            if (app != null) {
                return app.rule().displayName();
            }
        }
        return null;
    }

    /**
     * Swing {@code GoalBackAction.findNewestGoal}: the goal of the subtree that was changed last
     * (the highest node serial number), open and closed goals considered.
     */
    private static Goal findNewestGoal(Node subtree) {
        if (subtree == null) {
            return null;
        }
        Proof proof = subtree.proof();
        ImmutableList<Goal> closedGoals = proof.getClosedSubtreeGoals(subtree);
        ImmutableList<Goal> openGoals = proof.getSubtreeGoals(subtree);
        int closedID = -1;
        Goal closed = null;
        int openID = -1;
        Goal open = null;
        for (Goal g : closedGoals) {
            if (g.node().serialNr() > closedID) {
                closedID = g.node().serialNr();
                closed = g;
            }
        }
        for (Goal g : openGoals) {
            if (g.node().serialNr() > openID) {
                openID = g.node().serialNr();
                open = g;
            }
        }
        return closedID > openID ? closed : open;
    }

    /**
     * Counts a closed goal (called when a rule application produced no new goals).
     */
    public void closedAGoal() {
        goalsClosedByAutoMode++;
    }

    /**
     * @return the number of goals closed by the last auto mode run
     */
    public int getNrGoalsClosedByAutoMode() {
        return goalsClosedByAutoMode;
    }

    /**
     * Resets the closed-goal counter (called when an auto mode run starts).
     */
    public void resetNrGoalsClosedByHeuristics() {
        goalsClosedByAutoMode = 0;
    }

    /**
     * The mediator's proof tree listener (Swing {@code KeYMediatorProofTreeListener}): counts
     * closed goals, repairs the selection after pruning and logs proof closure (the notification
     * event follows in M3).
     */
    private final class MediatorProofTreeListener extends ProofTreeAdapter {
        @Override
        public void proofClosed(ProofTreeEvent e) {
            LOGGER.info("Proof closed: {}", e.getSource().name());
        }

        @Override
        public void proofPruned(ProofTreeEvent e) {
            FxUtil.runLater(() -> {
                Node selectedNode = keySelectionModel.getSelectedNode();
                if (selectedNode != null && !e.getSource().find(selectedNode)) {
                    keySelectionModel.setSelectedNode(e.getNode());
                }
            });
            OneStepSimplifier.refreshOSS(e.getSource());
        }

        @Override
        public void proofGoalsAdded(ProofTreeEvent e) {
            if (e.getGoals().isEmpty()) {
                // no new goals have been generated: the goal was closed
                closedAGoal();
            }
        }
    }

    /**
     * The mediator's rule application and auto mode listener (Swing {@code
     * KeYMediatorProofListener}): re-defaults the selection after interactive rule applications
     * so the views update, and tracks the auto mode state.
     */
    private final class RuleAppListenerProofListener implements RuleAppListener, AutoModeListener {

        @Override
        public void ruleApplied(ProofEvent e) {
            if (inAutoMode) {
                return;
            }
            if (e.getSource() == getSelectedProof()) {
                keySelectionModel.defaultSelection();
            }
        }

        @Override
        public void autoModeStarted(ProofEvent e) {
            inAutoMode = true;
            resetNrGoalsClosedByHeuristics();
            publishAutoModeRunning(true);
        }

        @Override
        public void autoModeStopped(ProofEvent e) {
            inAutoMode = false;
            publishAutoModeRunning(false);
        }
    }
}
