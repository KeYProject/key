/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.CopyOnWriteArrayList;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import de.uka.ilkd.key.control.AbstractProofControl;
import de.uka.ilkd.key.control.DefaultProofControl;
import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.RuleCompletionHandler;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.engine.TaskFinishedInfo;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.javafx.FxUtil;

import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Implementation of {@link de.uka.ilkd.key.control.UserInterfaceControl} which controls the
 * {@link MainWindowF} with the typical user interface of KeY: it routes the status, progress,
 * task, exception and warning callbacks of the core into the main window and hosts the registry
 * of interactive built-in rule completions.
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.WindowUserInterfaceControl} in the Swing module
 * {@code key.ui}. <b>Structural deviation</b> (forced by the module layout): the Swing original
 * extends {@code AbstractMediatorUserInterfaceControl} (a key.ui class which also provides the
 * {@code MediatorProofControl}; key.ui is not a dependency of key.ui.fx), while this port extends
 * the core {@link DefaultUserInterfaceControl} and implements {@link RuleCompletionHandler}
 * directly. Because {@code super(this)} is illegal Java, the constructor calls the handler-less
 * {@code super()} and builds its own {@link DefaultProofControl} with {@code this} as handler
 * (returned by {@link #getProofControl()}) — the mirror of the Swing wiring {@code
 * MediatorProofControl extends AbstractProofControl} constructed with
 * {@code super(ui, ui)} (MediatorProofControl.java:59-60,
 * AbstractMediatorUserInterfaceControl.java:51-52).
 * <p>
 * Completion dispatch (Swing WindowUserInterfaceControl.java:353-365): in auto mode the default
 * completion bypasses all dialogs (:354-356), otherwise the first registered completion whose
 * {@code canComplete} matches completes the app (:357-363) and the result is returned only when
 * it is complete (:364). A {@code null} or incomplete result makes the core
 * {@code AbstractProofControl} fall back to {@code completeBuiltInRuleAppByDefault}
 * (AbstractProofControl.java:496-511, :519-524) — the same silent-skip semantics as Swing for
 * apps the user cannot complete.
 * <p>
 * Deliberately deferred (see the port report): the load/save/recents methods of the Swing
 * original (the FX load path lives in {@code MainWindowF.startProofLoad}), the taclet-match
 * dialogs ({@code TacletMatchDialog}, a stub here), {@code selectProofObligation}
 * ({@code ProofManagementDialog}) and the progress bar (the FX status bar has no progress bar
 * yet).
 */
public class WindowUserInterfaceControlF extends DefaultUserInterfaceControl
        implements RuleCompletionHandler {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(WindowUserInterfaceControlF.class);

    private final MainWindowF mainWindow;

    /**
     * The registered completions, dispatched in registration order (Swing
     * {@code LinkedList<InteractiveRuleApplicationCompletion> completions},
     * WindowUserInterfaceControl.java:71-72). Copy-on-write: the registry is filled from the FX
     * thread while a completion may dispatch from a prover thread.
     */
    private final List<InteractiveRuleApplicationCompletionF> completions =
        new CopyOnWriteArrayList<>();

    /**
     * The registered {@link RuleCompletionHandler}s (consulted <em>after</em> all completions,
     * see {@link #register(RuleCompletionHandler)}).
     */
    private final List<RuleCompletionHandler> handlers = new CopyOnWriteArrayList<>();

    /**
     * The loaded proofs (bookkeeping for the later TaskTree/"Loaded Proofs" dockable; Swing
     * {@code mainWindow.addProblem(pa)}, WindowUserInterfaceControl.java:519-525, removal in
     * {@code proofDisposing} :507-512).
     */
    private final ObservableList<ProofAggregate> proofAggregates = FXCollections
            .observableArrayList();

    /**
     * The consulted {@link DefaultProofControl}: constructed explicitly in the constructor
     * because {@code super(this)} is illegal Java ("cannot reference this before the supertype
     * constructor has been called"); see the constructor comment.
     */
    private final DefaultProofControl proofControl;

    public WindowUserInterfaceControlF(MainWindowF mainWindow) {
        super();
        this.mainWindow = mainWindow;
        // seam: this control is its own RuleCompletionHandler — the mirror of the Swing wiring
        // MediatorProofControl extends AbstractProofControl constructed with super(ui, ui)
        // (MediatorProofControl.java:59-60). super(this) does not compile, so the consulted
        // proof control is built here explicitly (and returned by getProofControl).
        proofControl = new DefaultProofControl(this, this, this);
        // seam: completion registry — the FX merge point for interactive rule completions,
        // mirroring the Swing constructor registration (WindowUserInterfaceControl.java:74-82):
        // FunctionalOperationContractCompletion (:76), DependencyContractCompletion (:77),
        // LoopInvariantRuleCompletion (:78), BlockContractInternalCompletion(mainWindow) (:79),
        // BlockContractExternalCompletion(mainWindow) (:80), MergeRuleCompletion.INSTANCE (:81).
        // Those completions (and their dialogs) are ported by separate work items; they register
        // here via register(InteractiveRuleApplicationCompletionF) /
        // register(RuleCompletionHandler). With an empty registry the dispatch falls back to
        // the core default completion (the behavior of the former headless control).
    }

    // ------------------------------------------------------------------
    // completion registry (merge point for the interactive-completion agents)
    // ------------------------------------------------------------------

    /**
     * seam: the {@link DefaultProofControl} consulted by the core
     * ({@code KeYEnvironment.getProofControl});
     * it dispatches the interactive rule completions through this handler.
     */
    @Override
    public DefaultProofControl getProofControl() {
        return proofControl;
    }

    /**
     * Registers a completion at the end of the dispatch chain: the first registered completion
     * whose {@code canComplete(app)} matches completes the app (Swing dispatch
     * WindowUserInterfaceControl.java:357-363).
     *
     * @param completion the completion to register
     */
    public void register(InteractiveRuleApplicationCompletionF completion) {
        completions.add(completion);
    }

    /**
     * Registers a core {@link RuleCompletionHandler} (e.g. an interactive taclet-match
     * completion port) that is consulted after all registered
     * {@link InteractiveRuleApplicationCompletionF}s. Such a handler has no {@code canComplete};
     * by convention it returns {@code null} or the unchanged app if it does not want to complete
     * the app — in that case the core performs the default completion
     * ({@code AbstractProofControl.completeBuiltInRuleApp}, AbstractProofControl.java:496-511).
     *
     * @param handler the handler to register
     */
    public void register(RuleCompletionHandler handler) {
        handlers.add(handler);
    }

    /**
     * Dispatches the completion of a built-in rule application (port of Swing
     * WindowUserInterfaceControl.java:353-365): in auto mode the default completion bypasses all
     * dialogs (:354-356), otherwise the first matching completion (or, as fallback, a registered
     * {@link RuleCompletionHandler}) completes the app and the result is returned only when it
     * is complete (:364); an incomplete/null result makes the core fall back to the default
     * completion (AbstractProofControl.java:496-511).
     */
    @Override
    public IBuiltInRuleApp completeBuiltInRuleApp(IBuiltInRuleApp app, Goal goal, boolean forced) {
        if (mainWindow.getMediator().isInAutoMode()) {
            return AbstractProofControl.completeBuiltInRuleAppByDefault(app, goal, forced);
        }
        IBuiltInRuleApp result = app;
        for (InteractiveRuleApplicationCompletionF compl : completions) {
            if (compl.canComplete(app)) {
                result = compl.complete(app, goal, forced);
                break;
            }
        }
        for (RuleCompletionHandler handler : handlers) {
            IBuiltInRuleApp handled = handler.completeBuiltInRuleApp(app, goal, forced);
            if (handled != null && handled != app && handled.complete()) {
                result = handled;
                break;
            }
        }
        return (result != null && result.complete()) ? result : null;
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:329-338
     * ({@code completeAndApplyTacletMatch}): the Swing original opens the redesigned
     * {@code TacletMatchDialog} (or the classic one via
     * {@code ViewSettings.isUseClassicTacletDialog}
     * — a migration toggle). The FX taclet-match dialog suite is a separate port item; for now
     * the completion is reported and skipped (the core then keeps the app unapplied).
     */
    @Override
    public void completeAndApplyTacletMatch(TacletInstantiationModel[] models, Goal goal) {
        LOGGER.warn("The taclet match dialog is not yet ported to the JavaFX UI; "
            + "the taclet application is skipped ({} model(s))", models.length);
        NotificationManagerF.getInstance().notify(
            "The taclet match dialog arrives in a later milestone of the key.ui.fx rewrite.",
            NotificationManagerF.Kind.WARNING);
    }

    // ------------------------------------------------------------------
    // status & progress (ProblemLoaderControl / ProverTaskListener callbacks)
    // ------------------------------------------------------------------

    /**
     * Port of Swing WindowUserInterfaceControl.java:142-146 ({@code progressStarted} stops the
     * interface): the FX UI has no global interface lock yet (parity gap: the input freeze during
     * auto mode, see the main window audit).
     */
    @Override
    public void progressStarted(Object sender) {
        // no-op (Swing: mainWindow.getMediator().stopInterface(true))
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:147-150: no startInterface is needed, the
     * ProblemLoader re-enables the interface once loading is done.
     */
    @Override
    public void progressStopped(Object sender) {
        // no-op
    }

    /** Port of Swing WindowUserInterfaceControl.java:157-160. */
    @Override
    public void reportStatus(Object sender, String status, int progress) {
        // the FX status bar has no progress bar yet; the message is shown regardless
        reportStatus(sender, status);
    }

    /** Port of Swing WindowUserInterfaceControl.java:162-165 (mainWindow.setStatusLine). */
    @Override
    public void reportStatus(Object sender, String status) {
        FxUtil.runLater(() -> mainWindow.setStatusLine(status));
    }

    /** Port of Swing WindowUserInterfaceControl.java:167-170 (setStandardStatusLine). */
    @Override
    public void resetStatus(Object sender) {
        FxUtil.runLater(mainWindow::resetStatusLine);
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:152-155
     * ({@code IssueDialog.showExceptionDialog(mainWindow, e)}).
     */
    @Override
    public void reportException(Object sender, @Nullable ProofOblInput input, Exception e) {
        LOGGER.error("Exception reported by the proof machinery", e);
        FxUtil.runLater(() -> IssueDialogF.showExceptionDialog(mainWindow.getStage(), e));
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:294-299 (status line progress): the FX status
     * bar has no progress bar yet, so the position is logged only.
     */
    @Override
    public void taskProgress(int position) {
        super.taskProgress(position);
        LOGGER.debug("Task progress: {}", position);
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:301-305
     * ({@code mainWindow.setStatusLine(info.message(), info.size())}).
     */
    @Override
    public void taskStarted(TaskStartedInfo info) {
        super.taskStarted(info);
        reportStatus(this, info.message());
    }

    /** Port of Swing WindowUserInterfaceControl.java:307-315 (progress bar maximum). */
    @Override
    public void setMaximum(int maximum) {
        LOGGER.debug("Task progress maximum: {}", maximum);
    }

    /** Port of Swing WindowUserInterfaceControl.java:312-315 (progress bar position). */
    @Override
    public void setProgress(int progress) {
        LOGGER.debug("Task progress: {}", progress);
    }

    // ------------------------------------------------------------------
    // task finished (Swing taskFinishedInternal, WindowUserInterfaceControl.java:172-268)
    // ------------------------------------------------------------------

    /**
     * Port of Swing WindowUserInterfaceControl.java:172-177: the core may fire {@code
     * taskFinished} from a prover thread, so the handling is marshalled onto the FX thread (the
     * Swing original uses {@code SwingUtilities.invokeLater}).
     */
    @Override
    public void taskFinished(TaskFinishedInfo info) {
        super.taskFinished(info);
        FxUtil.runLater(() -> taskFinishedInternal(info));
    }

    private void taskFinishedInternal(TaskFinishedInfo info) {
        if (info != null && info.getSource() instanceof ProverCore) {
            if (!isAtLeastOneMacroRunning()) {
                resetStatus(this);
            }
            ApplyStrategyInfo<Proof, Goal> result = applyStrategyInfo(info);

            final Proof proof = (Proof) info.getProof();
            if (proof != null && !proof.isDisposed() && !proof.closed()
                    && mainWindow.getMediator().getSelectedProof() == proof) {
                Goal g = result.nonCloseableGoal();
                if (g == null) {
                    try {
                        g = proof.openGoals().head();
                    } catch (NoSuchElementException e) {
                        // all closed
                    }
                }
                if (g != null) {
                    // Swing: mainWindow.getMediator().goalChosen(g) (WindowUserInterfaceControl
                    // .java:198); the FX selection model is the goal re-choice
                    mainWindow.getSelectionModel().setSelectedGoal(g);
                    if (inStopAtFirstUncloseableGoalMode(proof)) {
                        // iff Stop on non-closeable Goal is selected a little popup is generated
                        // and the proof is stopped (WindowUserInterfaceControl.java:199-205)
                        new AutoDismissDialogF(mainWindow.getStage(),
                            "Couldn't close Goal Nr. " + g.node().serialNr()
                                + " automatically").show();
                    }
                }
                if (!isAtLeastOneMacroRunning()) {
                    showNotification("Automated proof search", info.toString());
                }
            }
            // Swing: mainWindow.displayResults(info.toString()) (:210)
            mainWindow.setStatusLine(info.toString());
        } else if (info != null && info.getSource() instanceof ProofMacro macro) {
            if (!isAtLeastOneMacroRunning()) {
                // Swing hides the status progress here (:213); the FX status bar has none yet
                mainWindow.setStatusLine(info.toString());
                final Proof proof = (Proof) info.getProof();
                if (proof != null && !proof.closed()
                        && mainWindow.getMediator().getSelectedProof() == proof) {
                    Goal g = proof.openGoals().head();
                    mainWindow.getSelectionModel().setSelectedGoal(g);
                    if (inStopAtFirstUncloseableGoalMode(proof)) {
                        new AutoDismissDialogF(mainWindow.getStage(),
                            "Couldn't close Goal Nr. " + g.node().serialNr()
                                + " automatically").show();
                    }
                    if (!isAtLeastOneMacroRunning()) {
                        showNotification(macro.getName(), info.toString());
                    }
                }
            }
        } else if (info != null && info.getResult() instanceof Throwable result) {
            // ProblemLoader branch (Swing WindowUserInterfaceControl.java:236-244): load errors
            // surface in the IssueDialog
            resetStatus(this);
            LOGGER.error("", result);
            if (result instanceof ParseCancellationException) {
                result = result.getCause();
            }
            IssueDialogF.showExceptionDialog(mainWindow.getStage(), result);
        } else if (info != null
                && info.getSource() instanceof de.uka.ilkd.key.proof.io.AbstractProblemLoader) {
            // successful load (Swing WindowUserInterfaceControl.java:245-261): the proof script
            // and macro application of the Swing original are deferred in the FX load path
            resetStatus(this);
        } else {
            resetStatus(this);
            if (info != null && !info.toString().isEmpty()) {
                mainWindow.setStatusLine(info.toString());
            }
        }
    }

    @SuppressWarnings("unchecked")
    private static ApplyStrategyInfo<Proof, Goal> applyStrategyInfo(TaskFinishedInfo info) {
        return (ApplyStrategyInfo<Proof, Goal>) info.getResult();
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:276-286
     * ({@code showNotification}): shows the notification as a toast when the
     * {@code notificationAfterMacro} view setting allows it ({@code Always} always, {@code When
     * not focused} only when the main window has no focus; the Swing original uses a system tray
     * notification — a documented cosmetic difference of the FX UI).
     */
    private void showNotification(String title, String text) {
        String mode =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().notificationAfterMacro();
        if (mode.equals(ViewSettings.NOTIFICATION_ALWAYS)) {
            NotificationManagerF.getInstance().notify(title + ": " + text);
        } else if (mode.equals(ViewSettings.NOTIFICATION_UNFOCUSED)) {
            if (!mainWindow.getStage().isFocused()) {
                NotificationManagerF.getInstance().notify(title + ": " + text);
            }
        }
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:288-292: whether the strategy of the proof is
     * in the "stop on non-closeable goal" mode.
     */
    protected boolean inStopAtFirstUncloseableGoalMode(Proof proof) {
        return proof.getSettings().getStrategySettings().getActiveStrategyProperties()
                .getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }

    // ------------------------------------------------------------------
    // proof lifecycle (register/dispose — bookkeeping for the later TaskTree dockable)
    // ------------------------------------------------------------------

    /**
     * Port of Swing WindowUserInterfaceControl.java:519-525
     * ({@code registerProofAggregate}): registers the proof-disposed listeners (the super
     * implementation, AbstractUserInterfaceControl.java:300-304), records the aggregate for the
     * later TaskTree/"Loaded Proofs" dockable (Swing {@code mainWindow.addProblem}) and resets
     * the status line (Swing {@code setStandardStatusLine}). The Swing {@code
     * getMediator().fireProofLoaded} has no FX counterpart (the FX views observe the selection
     * model).
     */
    @Override
    public void registerProofAggregate(ProofAggregate pa) {
        super.registerProofAggregate(pa);
        FxUtil.runLater(() -> {
            proofAggregates.add(pa);
            mainWindow.resetStatusLine();
        });
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:507-512 ({@code proofDisposing}): removes the
     * proof from the UI bookkeeping. Note: the core {@code UserInterfaceControl} does not declare
     * {@code proofDisposing} (the Swing method is on {@code AbstractMediatorUserInterfaceControl}
     * in key.ui), so this is a plain hook for the later TaskTree/"Loaded Proofs" port.
     */
    public void proofDisposing(ProofDisposedEvent e) {
        FxUtil.runLater(() -> proofAggregates
                .removeIf(pa -> List.of(pa.getProofs()).contains(e.getSource())));
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:620-623
     * ({@code IssueDialog.showWarningsIfNecessary}).
     */
    @Override
    public void reportWarnings(ImmutableSet<PositionedString> warnings) {
        FxUtil.runLater(
            () -> IssueDialogF.showWarningsIfNecessary(mainWindow.getStage(), warnings));
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:633-641 ({@code showIssueDialog}): shows the
     * given issues without the "ignore warnings" affordance (title "Issues", critical).
     */
    @Override
    public void showIssueDialog(java.util.Collection<PositionedString> issues) {
        IssueDialogF.showIssues(mainWindow.getStage(), "Issues", issues);
    }

    /**
     * Port of Swing WindowUserInterfaceControl.java:514-517 ({@code selectProofObligation}
     * opens the {@code ProofManagementDialog}): the proof management dialog is a deferred port
     * item, so no proof obligation can be selected (the default headless behavior).
     */
    @Override
    public boolean selectProofObligation(
            de.uka.ilkd.key.proof.init.InitConfig initConfig) {
        return false;
    }

    // ------------------------------------------------------------------
    // bookkeeping accessors (for the later TaskTree/"Loaded Proofs" dockable)
    // ------------------------------------------------------------------

    /**
     * @return the observable list of loaded proof aggregates (Swing
     *         {@code MainWindow.getProofList()}); proofs are removed when they are disposed
     */
    public ObservableList<ProofAggregate> getProofAggregates() {
        return proofAggregates;
    }

    /**
     * @return {@code true} if the given proof is registered (Swing
     *         {@code mainWindow.getProofList().containsProof(proof)}, used by the Swing
     *         {@code isAutoModeSupported} override, WindowUserInterfaceControl.java:91-94)
     */
    public boolean containsProof(Proof proof) {
        return proofAggregates.stream().anyMatch(pa -> List.of(pa.getProofs()).contains(proof));
    }
}
