/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.EventObject;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.Consumer;
import javax.swing.*;
import javax.swing.event.EventListenerList;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.GUIListener;
import de.uka.ilkd.key.gui.UserActionListener;
import de.uka.ilkd.key.gui.actions.useractions.UserAction;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.ui.AbstractMediatorUserInterfaceControl;
import de.uka.ilkd.key.util.ThreadUtilities;

import org.key_project.proof.LocationVariableTracker;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.lookup.Lookup;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * The {@link KeYMediator} provides control logic for the user interface implemented in Swing.
 * <p>
 * <strong>Attention: </strong> Logic to apply rules has to be implemented user interface
 * independent in the {@link ProofControl}!
 */
public class KeYMediator {

    /** The user interface */
    private final AbstractMediatorUserInterfaceControl ui;

    /** the notation info used to print sequents */
    private final NotationInfo notationInfo;

    /** listenerList with to gui listeners */
    private final EventListenerList listenerList = new EventListenerList();

    /** listens to the proof */
    private final KeYMediatorProofListener proofListener;

    /** listens to the ProofTree */
    private final KeYMediatorProofTreeListener proofTreeListener;

    /**
     * current proof and node the user works with. All user interaction is relative to this model
     */
    private final KeYSelectionModel keySelectionModel;

    /**
     * Registered proof load listeners.
     *
     * @see #fireProofLoaded(Proof)
     */
    private final Collection<Consumer<Proof>> proofLoadListeners = new ArrayList<>();

    private TacletFilter filterForInteractiveProving;

    /**
     * An optional used {@link AutoSaver}.
     */
    private AutoSaver autoSaver = AutoSaver.getDefaultInstance();

    /**
     * Currently opened proofs.
     */
    private final List<Proof> currentlyOpenedProofs = new CopyOnWriteArrayList<>();

    /**
     * boolean flag indicating if the GUI is in auto mode
     */
    private volatile boolean inAutoMode;

    /**
     * Currently activated listeners for user actions. Notified whenever a user action is applied.
     *
     * @see #fireActionPerformed(UserAction)
     */
    private final Collection<UserActionListener> userActionListeners = new ArrayList<>();

    /**
     * creates the KeYMediator with a reference to the application's main frame and the current
     * proof settings
     */
    public KeYMediator(AbstractMediatorUserInterfaceControl ui) {
        this.ui = ui;

        notationInfo = new NotationInfo();
        proofListener = new KeYMediatorProofListener();
        proofTreeListener = new KeYMediatorProofTreeListener();
        keySelectionModel = new KeYSelectionModel(this);

        ui.getProofControl().addAutoModeListener(proofListener);

        registerProofLoadListener(LocationVariableTracker::handleProofLoad);
    }

    /**
     * Register a proof load listener. Will be called whenever a new proof is loaded, but before
     * it is replayed. The listener MUST be able to accept the same proof twice!
     *
     * @param listener callback
     */
    public synchronized void registerProofLoadListener(Consumer<Proof> listener) {
        proofLoadListeners.add(listener);
    }

    /**
     * returns the used NotationInfo
     *
     * @return the used NotationInfo
     */
    public NotationInfo getNotationInfo() {
        return notationInfo;
    }

    /** returns the Services with the java service classes */
    public Services getServices() {
        Proof selectedProof = getSelectedProof();
        return selectedProof != null ? selectedProof.getServices() : null;
    }

    public void setAutoSave(int interval) {
        autoSaver = interval > 0 ? new AutoSaver(interval, true) : null;
    }

    public boolean ensureProofLoaded() {
        return getSelectedProof() != null;
    }

    /**
     * Returns a filter that is used for filtering taclets that should not be showed while
     * interactive proving.
     */
    public TacletFilter getFilterForInteractiveProving() {
        if (filterForInteractiveProving == null) {
            filterForInteractiveProving = new TacletFilter() {

                @Override
                protected boolean filter(Taclet taclet) {
                    for (String name : JoinProcessor.SIMPLIFY_UPDATE) {
                        if (name.equals(taclet.name().toString())) {
                            return false;
                        }
                    }
                    return true;
                }

            };
        }
        return filterForInteractiveProving;
    }

    public void setBack(Node node) {
        getUI().getProofControl().pruneTo(node);
        finishSetBack(node.proof());
        keySelectionModel.setSelectedNode(node);
    }

    public void setBack(Goal goal) {
        if (getSelectedProof() != null) {
            getUI().getProofControl().pruneTo(goal);
            final Proof proof = goal.proof();
            finishSetBack(proof);
            Node node = goal.node() == proof.root() ? goal.node() : goal.node().parent();
            keySelectionModel.setSelectedNode(node);
        }
    }

    private void finishSetBack(final Proof proof) {
        TaskFinishedInfo info =
            new DefaultTaskFinishedInfo(this, null, proof, 0, 0, getNrGoalsClosedByAutoMode()) {
                @Override
                public String toString() {
                    return "Proof has been pruned: "
                        + (proof.openGoals().size() == 1 ? "one open goal remains."
                                : (proof.openGoals().size() + " open goals remain."));
                }
            };
        this.ui.taskFinished(info);
        if (!proof.isDisposed()) {
            ServiceCaches caches = proof.getServices().getCaches();
            caches.getTermTacletAppIndexCache().clear();
            caches.getBetaCandidates().clear(); // TODO: Is this required since the strategy is
                                                // instantiated everytime again?
            caches.getIfThenElseMalusCache().clear(); // TODO: Is this required since the strategy
                                                      // is instantiated everytime again?
        }
    }

    /**
     * Selects the specified proof and initializes it.
     * <br/>
     * This method is called by the selection model, which fires the event.
     * The method itself does not fire
     * {@link KeYSelectionListener#selectedProofChanged(KeYSelectionEvent)}
     *
     * @param newProof the proof to select.
     * @param previousProof the previously selected proof
     */
    void setProof(Proof newProof, Proof previousProof) {
        if (previousProof == newProof) {
            return;
        }

        if (previousProof != null) {
            previousProof.removeProofTreeListener(proofTreeListener);
            previousProof.removeRuleAppListener(proofListener);
        }
        if (newProof != null) {
            notationInfo.setAbbrevMap(newProof.abbreviations());
        }
        if (newProof != null) {
            newProof.addProofTreeListener(proofTreeListener);
            newProof.addRuleAppListener(proofListener);
        }
        if (getAutoSaver() != null) {
            getAutoSaver().setProof(newProof);
        }

        OneStepSimplifier.refreshOSS(newProof);
    }

    /**
     * sets the maximum number of rule applications allowed in automatic mode
     *
     * @param steps an int setting the limit
     */
    public void setMaxAutomaticSteps(int steps) {
        if (getSelectedProof() != null) {
            getSelectedProof().getSettings().getStrategySettings().setMaxSteps(steps);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    /**
     * returns the maximum number of rule applications allowed in automatic mode
     *
     * @return the maximum number of rule applications allowed in automatic mode
     */
    public int getMaxAutomaticSteps() {
        if (getSelectedProof() != null) {
            return getSelectedProof().getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    /**
     * adds a listener to the KeYSelectionModel, so that the listener will be informed if the proof
     * or node the user has selected changed
     *
     * @param listener the KeYSelectionListener to add
     */
    public void addKeYSelectionListener(KeYSelectionListener listener) {
        keySelectionModel.addKeYSelectionListener(listener);
    }

    /**
     * adds a listener to the KeYSelectionModel, so that the listener will be informed if the proof
     * or node the user has selected changed
     *
     * adds the listener only if it not already registered
     *
     * @param listener the KeYSelectionListener to add
     */
    public void addKeYSelectionListenerChecked(KeYSelectionListener listener) {
        keySelectionModel.addKeYSelectionListenerChecked(listener);
    }

    /**
     * removes a listener from the KeYSelectionModel
     *
     * @param listener the KeYSelectionListener to be removed
     */
    public void removeKeYSelectionListener(KeYSelectionListener listener) {
        keySelectionModel.removeKeYSelectionListener(listener);
    }

    /**
     * adds a listener to GUI events
     *
     * @param listener the GUIListener to be added
     */
    public void addGUIListener(GUIListener listener) {
        listenerList.add(GUIListener.class, listener);
    }

    /**
     * adds a listener to GUI events
     *
     * @param listener the GUIListener to be added
     */
    public void removeGUIListener(GUIListener listener) {
        listenerList.remove(GUIListener.class, listener);
    }

    public void addInterruptedListener(InterruptListener listener) {
        listenerList.add(InterruptListener.class, listener);
    }

    public void removeInterruptedListener(InterruptListener listener) {
        listenerList.remove(InterruptListener.class, listener);
    }

    /**
     * sets the current goal
     *
     * @param goal the Goal being displayed in the view of the sequent
     */
    public void goalChosen(Goal goal) {
        keySelectionModel.setSelectedGoal(goal);
    }

    /**
     * returns the user interface
     *
     * @return the user interface
     */
    public AbstractMediatorUserInterfaceControl getUI() {
        return ui;
    }

    /**
     * notifies that a node that is not a goal has been chosen
     *
     * @param node the node being displayed in the view of the sequent
     */
    public void nonGoalNodeChosen(Node node) {
        keySelectionModel.setSelectedNode(node);
    }

    /**
     * called to ask for modal access
     *
     * @param src Object that is the asking component
     */
    public synchronized void requestModalAccess(Object src) {
        fireModalDialogOpened(new EventObject(src));
    }

    /**
     * called if no more modal access is needed
     *
     * @param src Object that is the asking component
     */
    public synchronized void freeModalAccess(Object src) {
        fireModalDialogClosed(new EventObject(src));
    }

    /**
     * fires the request of a GUI component for modal access this can be used to disable all views
     * even if the GUI component has no built in modal support
     */
    public synchronized void fireModalDialogOpened(EventObject e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == GUIListener.class) {
                ((GUIListener) listeners[i + 1]).modalDialogOpened(e);
            }
        }
    }

    /**
     * fires that a GUI component that has asked for modal access has been closed, so views can be
     * enabled again
     */
    public synchronized void fireModalDialogClosed(EventObject e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == GUIListener.class) {
                ((GUIListener) listeners[i + 1]).modalDialogClosed(e);
            }
        }
    }

    /**
     * Fires the shut-down event.
     */
    public synchronized void fireShutDown(EventObject e) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == GUIListener.class) {
                ((GUIListener) listeners[i + 1]).shutDown(e);
            }
        }
    }

    /**
     * Fire the proof loaded event.
     *
     * @param p the proof that was just loaded and is about to be replayed
     */
    public synchronized void fireProofLoaded(Proof p) {
        if (p == null) {
            return;
        }
        for (Consumer<Proof> listener : proofLoadListeners) {
            listener.accept(p);
        }
    }

    /**
     * returns the current selected proof
     *
     * @return the current selected proof
     */
    @Nullable
    public Proof getSelectedProof() {
        return keySelectionModel.getSelectedProof();
    }

    /**
     * returns the current selected goal
     *
     * @return the current selected goal
     */
    public Goal getSelectedGoal() {
        return keySelectionModel.getSelectedGoal();
    }

    /**
     * returns the current selected goal
     *
     * @return the current selected goal
     */
    public KeYSelectionModel getSelectionModel() {
        return keySelectionModel;
    }

    /**
     * returns the current selected node
     *
     * @return the current selected node
     */
    public Node getSelectedNode() {
        return keySelectionModel.getSelectedNode();
    }

    /**
     * Interrupts all registered {@link InterruptListener}s.
     */
    public void interrupt() {
        for (InterruptListener listener : listenerList.getListeners(InterruptListener.class)) {
            listener.interruptionPerformed();
        }
    }

    /**
     * Switches interactive mode on or off.
     *
     * @param b true iff interactive mode is to be turned on
     */
    public void setInteractive(boolean b) {
        if (getSelectedProof() != null) {
            if (b) {
                getSelectedProof().setRuleAppIndexToInteractiveMode();
            } else {
                getSelectedProof().setRuleAppIndexToAutoMode();
            }
        }
    }

    private int goalsClosedByAutoMode = 0;

    public void closedAGoal() {
        goalsClosedByAutoMode++;
    }

    public int getNrGoalsClosedByAutoMode() {
        return goalsClosedByAutoMode;
    }

    public void resetNrGoalsClosedByHeuristics() {
        goalsClosedByAutoMode = 0;
    }

    public synchronized void stopInterface(boolean fullStop) {
        final boolean b = fullStop;
        Runnable interfaceSignaller = () -> {
            ui.notifyAutoModeBeingStarted();
            if (b) {
                inAutoMode = true;
            }
        };
        ThreadUtilities.invokeAndWait(interfaceSignaller);
    }

    public synchronized void startInterface(boolean fullStop) {
        final boolean b = fullStop;
        SwingUtilities.invokeLater(() -> {
            if (b) {
                inAutoMode = false;
            }
            ui.notifyAutomodeStopped();
        });
    }

    /**
     * performs the standard preparations for starting automode
     * <ol>
     * <li>call {@code this.stopInterface(fullstop)}</li>
     * <li>call {@code getUI().getProofControl().fireAutoModeStarted(proof)}</li>
     * <li>call {@code this.setInteractive(interactive)}</li>
     * </ol>
     *
     * @param proof the {@link Proof} to be worked on
     * @param fullStop if a full freeze of the interface is requested
     * @param interactive whether the needed taclet index is for interactove or automatic use
     *        (normally false)
     */
    public void initiateAutoMode(Proof proof, boolean fullStop, boolean interactive) {
        stopInterface(fullStop);
        getUI().getProofControl().fireAutoModeStarted(new ProofEvent(proof));
        setInteractive(interactive);
    }

    /**
     * performs the standard preparations for starting automode
     * <ol>
     * <li>call {@code this.startInterface(fullstop)}</li>
     * <li>call {@code getUI().getProofControl().fireAutoModeStopped(proof)}</li>
     * <li>call {@code this.setInteractive(interactive)}</li>
     * <li>select a node/proof by running the given selector (null means the default selection is
     * used)</li>
     * </ol>
     *
     * @param proof the {@link Proof} to be worked on
     * @param fullStop if a full freeze of the interface is requested
     * @param interactive whether the needed taclet index is for interactive or automatic use shoul
     *        be selected
     *        (normally true)
     * @param selection a Runnable that selects the correct node after unfreezing the interface
     */
    public void finishAutoMode(Proof proof, boolean fullStop, boolean interactive,
            Runnable selection) {
        setInteractive(interactive);
        startInterface(fullStop);
        getUI().getProofControl().fireAutoModeStopped(new ProofEvent(proof));
        if (selection == null) {
            keySelectionModel.defaultSelection();
        } else {
            selection.run();
        }
    }


    /**
     * Checks if the auto mode is currently running.
     *
     * @return {@code true} auto mode is running, {@code false} auto mode is not running.
     */
    public boolean isInAutoMode() {
        return inAutoMode;
    }

    @Nullable
    private Lookup userData;

    /**
     * Retrieves a user-defined data.
     *
     * @param service the class for which the data were registered
     * @param <T> any class
     * @return null or the previous data
     * @see #register(Object, Class)
     */
    public <T> T lookup(Class<T> service) {
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
     * Register a user-defined data in this node info.
     *
     * @param obj an object to be registered
     * @param service the key under it should be registered
     * @param <T>
     */
    public <T> void register(T obj, Class<T> service) {
        getUserData().register(obj, service);
    }

    /**
     * Remove a previous registered user-defined data.
     *
     * @param obj registered object
     * @param service the key under which the data was registered
     * @param <T> arbitray object
     */
    public <T> void deregister(T obj, Class<T> service) {
        if (userData != null) {
            userData.deregister(obj, service);
        }
    }

    /**
     * Get the associated lookup of user-defined data.
     *
     * @return
     */
    public @NonNull Lookup getUserData() {
        if (userData == null) {
            userData = new Lookup();
        }
        return userData;
    }

    class KeYMediatorProofTreeListener extends ProofTreeAdapter {
        private boolean pruningInProcess;

        @Override
        public void proofClosed(ProofTreeEvent e) {
            Proof p = e.getSource();
            assert p.name().equals(getSelectedProof().name());
            assert p.closed();
            KeYMediator.this.notify(new ProofClosedNotificationEvent(e.getSource()));
        }

        public void proofPruningInProcess(ProofTreeEvent e) {
            pruningInProcess = true;
        }

        @Override
        public void proofPruned(final ProofTreeEvent e) {
            SwingUtilities.invokeLater(() -> {
                if (!e.getSource().find(getSelectedNode())) {
                    keySelectionModel.setSelectedNode(e.getNode());
                }
            });
            OneStepSimplifier.refreshOSS(e.getSource());
            pruningInProcess = false;
        }

        @Override
        public void proofGoalsAdded(ProofTreeEvent e) {
            ImmutableList<Goal> newGoals = e.getGoals();
            // Check for a closed goal ...
            if (newGoals.isEmpty()) {
                // No new goals have been generated ...
                closedAGoal();
            }
        }

        @Override
        public void proofStructureChanged(ProofTreeEvent e) {}
    }

    private final class KeYMediatorProofListener implements RuleAppListener, AutoModeListener {

        /** invoked when a rule has been applied */
        @Override
        public void ruleApplied(ProofEvent e) {
            if (isInAutoMode()) {
                return;
            }
            if (e.getSource() == getSelectedProof()) {
                keySelectionModel.defaultSelection();
            }
        }

        /**
         * invoked if automatic execution has started
         */
        @Override
        public void autoModeStarted(ProofEvent e) {
            resetNrGoalsClosedByHeuristics();
        }

        /**
         * invoked if automatic execution has stopped
         */
        @Override
        public void autoModeStopped(ProofEvent e) {
        }
    }

    /*
     * Disable certain actions until a proof is loaded.
     */
    public void enableWhenProofLoaded(final Action a) {
        a.setEnabled(getSelectedProof() != null);
        addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                a.setEnabled(e.getSource().getSelectedProof() != null);
            }
        });
    }

    /**
     * Disable certain actions until a proof is loaded. This is a workaround for a broken proof
     * macro menu in the GUI. Remove this method as soon as another solution can be found.
     */
    @Deprecated
    public void enableWhenProofLoaded(final javax.swing.AbstractButton a) {
        a.setEnabled(getSelectedProof() != null);
        addKeYSelectionListener(new KeYSelectionListener() {

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                a.setEnabled(e.getSource().getSelectedProof() != null);
            }
        });
    }

    /**
     * takes a notification event and informs the notification manager
     *
     * @param event the NotificationEvent
     */
    public void notify(NotificationEvent event) {
        ui.notify(event);
    }

    /** return the chosen profile */
    public Profile getProfile() {
        Proof selectedProof = getSelectedProof();
        if (selectedProof != null) {
            return selectedProof.getServices().getProfile();
        } else {
            return AbstractProfile.getDefaultProfile();
        }
    }

    /**
     * besides the number of rule applications it is possible to define a timeout after which rule
     * application shall be terminated
     *
     * @return the time in ms after which automatic rule application stops
     */
    public long getAutomaticApplicationTimeout() {
        if (getSelectedProof() != null) {
            return getSelectedProof().getSettings().getStrategySettings().getTimeout();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getTimeout();
        }
    }

    /**
     * sets the time out after which automatic rule application stops
     *
     * @param timeout a long specifying the timeout time in ms
     */
    public void setAutomaticApplicationTimeout(long timeout) {
        if (getSelectedProof() != null) {
            getSelectedProof().getSettings().getStrategySettings().setTimeout(timeout);
        }
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
    }

    // /**
    // * returns the prover task listener of the main frame
    // */
    // // TODO used 1 time, drop it? (MU)
    // public ProverTaskListener getProverTaskListener() {
    // return ui;
    // }


    /**
     * Returns the {@link AutoSaver} to use.
     *
     * @return The {@link AutoSaver} to use or {@code null} if no {@link AutoSaver} should be used.
     */
    public AutoSaver getAutoSaver() {
        return autoSaver;
    }

    /**
     * Provides a list of currently opened view.
     * <p>
     * You can use this instance directly inside your components or add a listener to observe
     * changes.
     *
     */
    public @NonNull List<Proof> getCurrentlyOpenedProofs() {
        return currentlyOpenedProofs;
    }

    /**
     * Add another listener for user actions.
     *
     * @param listener listener object
     */
    public void addUserActionListener(UserActionListener listener) {
        userActionListeners.add(listener);
    }

    /**
     * Notify all user action listeners about a performed action.
     *
     * @param action the user action
     */
    public void fireActionPerformed(UserAction action) {
        for (UserActionListener listener : userActionListeners) {
            listener.actionPerformed(action);
        }
    }
}
