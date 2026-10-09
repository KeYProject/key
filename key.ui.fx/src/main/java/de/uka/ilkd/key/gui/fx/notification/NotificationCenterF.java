/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.notification;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import javafx.application.Platform;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.gui.fx.notification.events.AbandonTaskEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ExceptionFailureEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ExitKeYEventF;
import de.uka.ilkd.key.gui.fx.notification.events.GeneralFailureEventF;
import de.uka.ilkd.key.gui.fx.notification.events.GeneralInformationEventF;
import de.uka.ilkd.key.gui.fx.notification.events.NotificationEventF;
import de.uka.ilkd.key.gui.fx.notification.events.ProofClosedNotificationEventF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The notification manager controls the list of active notification tasks. It receives KeY
 * system events and looks for an appropriate task.
 * <p>
 * Port of the Swing original {@code key.ui/src/main/java/de/uka/ilkd/key/gui/notification/
 * NotificationManager.java}. Naming deviation: the FX toast sink
 * {@link NotificationManagerF} already occupies the Swing class name, so the manager of the
 * event/task/action framework is called {@code NotificationCenterF}.
 * <p>
 * App-level wiring status (parity audit {@code parity-unported-dialogs.md} §10): the proof-closed
 * and "Automated proof search" triggers are wired through
 * {@link #afterAutoModeFinished(Proof, boolean)} (called from the FX auto-mode-stop hook);
 * the exception routing (termmenu/S4: {@code ExceptionFailureEventF} dispatch in
 * {@code MainWindowF.setOnFailed}, the task registered in {@link #setDefaultNotifications()})
 * is wired; the exit/abandon triggers are not ported yet.
 */
public final class NotificationCenterF {

    private static final Logger LOGGER = LoggerFactory.getLogger(NotificationCenterF.class);

    private static final NotificationCenterF INSTANCE = new NotificationCenterF();

    /** list of notification tasks */
    private final Map<NotificationEventIDF, NotificationTaskF> notificationTasks =
        new EnumMap<>(NotificationEventIDF.class);

    /** true if we are currently in automode */
    private boolean autoMode = false;

    private final NotificationListenerF notificationListener = new NotificationListenerF();

    private NotificationCenterF() {
        setDefaultNotifications();
    }

    /**
     * @return the global notification framework instance
     */
    public static NotificationCenterF getInstance() {
        return INSTANCE;
    }

    /**
     * installs the default notification tasks, mirroring the Swing
     * {@code NotificationManager.setDefaultNotification}.
     */
    public void setDefaultNotifications() {
        notificationTasks.clear();
        addNotificationTask(new ProofClosedNotificationF());
        addNotificationTask(new GeneralFailureNotificationF());
        addNotificationTask(new GeneralInformationNotificationF());
        addNotificationTask(new AbandonNotificationF());
        addNotificationTask(new ExitKeYNotificationF());
        // termmenu/S4: the exception-failure task is registered by default. This resolves the
        // TODO-merge left by the seam agent: MainWindowF.setOnFailed routes load failures
        // through handleNotificationEvent(new ExceptionFailureEventF(...)).
        //
        // The Swing FIXME (ported from NotificationManager.setDefaultNotification) is not
        // applicable to the FX port: the Swing ExceptionFailureNotification opened a *dialog*
        // (ExceptionFailureNotificationDialog -> IssueDialog.showExceptionDialog), causing a
        // double dialog for parser errors (the ProblemLoader branch already surfaces the
        // IssueDialog); the FX ExceptionFailureNotificationF only shows an error *toast*, so
        // dialog + toast is the intended surface (Swing parity: WindowUserInterfaceControl
        // reports parser errors in the IssueDialog while the toast keeps the notification sink).
        addNotificationTask(new ExceptionFailureNotificationF());
    }

    /**
     * adds a notification task to this manager
     *
     * @param task the NotificationTaskF to be added
     */
    public void addNotificationTask(NotificationTaskF task) {
        notificationTasks.put(task.getEventID(), task);
    }

    /**
     * removes the given notification task from the list of active tasks
     *
     * @param task the task to be removed
     */
    public void removeNotificationTask(NotificationTaskF task) {
        removeNotificationTask(task.getEventID());
    }

    /**
     * Removes the {@link NotificationTaskF} with the given {@link NotificationEventIDF}.
     * <p>
     * This functionality is used by the Eclipse integration (Swing parity,
     * NotificationManager.java:87-93).
     *
     * @param eventID The {@link NotificationEventIDF} to remove its {@link NotificationTaskF}.
     * @return The removed {@link NotificationTaskF} or {@code null} if none was available.
     */
    public NotificationTaskF removeNotificationTask(NotificationEventIDF eventID) {
        return notificationTasks.remove(eventID);
    }

    /**
     * @return true if the prover is currently in automode
     */
    public boolean inAutoMode() {
        return autoMode;
    }

    /**
     * @return the auto mode listener tracking the auto-mode state; register it on the proof
     *         control like the Swing {@code NotificationManager} constructor does
     *         (NotificationManager.java:99-101)
     */
    public AutoModeListener notificationListener() {
        return notificationListener;
    }

    /**
     * dispatches the received notification event and triggers the corresponding task
     *
     * @param event the notification event
     */
    public void handleNotificationEvent(NotificationEventF event) {
        NotificationTaskF notificationTask = notificationTasks.get(event.getEventID());
        if (notificationTask != null) {
            notificationTask.execute(event, this);
        }
    }

    /**
     * The minimal FX wiring of the app-level notification triggers that Swing performs after an
     * automatic strategy run (called from the FX auto-mode-stop hook,
     * {@code MainWindowF.refreshViewsFromFinalState}):
     * <ul>
     * <li>the proof-closed notification (Swing: {@code KeYMediator.KeYMediatorProofTreeListener
     * .proofClosed} fires a {@code ProofClosedNotificationEvent}, KeYMediator.java:641-646),</li>
     * <li>the "Automated proof search" information (Swing:
     * {@code WindowUserInterfaceControl.taskFinishedInternal → showNotification},
     * WindowUserInterfaceControl.java:199-207), gated by the
     * {@link ViewSettings#notificationAfterMacro()} setting with the same ALWAYS / "When not
     * focused" / NEVER semantics.</li>
     * </ul>
     *
     * @param proof the proof the automatic run finished on (may be {@code null})
     * @param windowFocused whether the main window is currently focused (Swing parity:
     *        {@code MainWindow.isActive()} in the NOTIFICATION_UNFOCUSED case)
     */
    public void afterAutoModeFinished(Proof proof, boolean windowFocused) {
        if (proof == null || proof.isDisposed()) {
            return;
        }
        if (proof.closed()) {
            handleNotificationEvent(new ProofClosedNotificationEventF(proof));
        }
        String mode =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().notificationAfterMacro();
        if (mode.equals(ViewSettings.NOTIFICATION_NEVER)) {
            return;
        }
        if (mode.equals(ViewSettings.NOTIFICATION_UNFOCUSED) && windowFocused) {
            return;
        }
        // Swing passes the TaskFinishedInfo.toString() of the strategy run; the FX auto-mode
        // stop hook only has the proof, so the final statistics are used as the body instead
        // (documented deviation)
        String summary;
        try {
            summary = proof.getStatistics().toString();
        } catch (RuntimeException e) {
            summary = "finished";
        }
        handleNotificationEvent(
            new GeneralInformationEventF("Automated proof search", summary));
    }

    /**
     * Development self-test ({@code key.fx.verify.notifications}): exercises the framework the
     * way the Swing original is used, without touching the default task registry.
     * <ol>
     * <li>a task dispatches its actions when executed outside auto mode, synchronously on the
     * FX application thread (parity with the EDT check in NotificationTask.execute),</li>
     * <li>a task not marked {@code automodeEnabledTask} is skipped while in auto mode,</li>
     * <li>a task marked {@code automodeEnabledTask} runs while in auto mode,</li>
     * <li>the default registry contains the five default tasks (Swing
     * {@code setDefaultNotification}),</li>
     * <li>{@link #handleNotificationEvent} routes a registered and an unregistered event id
     * without failure.</li>
     * </ol>
     * The final dispatch of a real information and failure event additionally makes the toast
     * sink show the two severity variants, so the run is visible on screen (screenshot check).
     *
     * @return {@code "PASS"} or {@code "FAIL: <reason>"}, in the style of the other
     *         {@code key.fx.verify.*} self-tests
     */
    public String verifyFramework() {
        if (!Platform.isFxApplicationThread()) {
            return "FAIL: self-test must run on the JavaFX application thread";
        }
        List<NotificationEventF> received = new ArrayList<>();
        NotificationTaskF task = new NotificationTaskF() {
            @Override
            public NotificationEventIDF getEventID() {
                return NotificationEventIDF.GENERAL_INFORMATION;
            }
        };
        task.addNotificationAction(event -> {
            received.add(event);
            return true;
        });

        // 1. plain dispatch outside auto mode, synchronous on the FX thread
        GeneralInformationEventF first = new GeneralInformationEventF("self-test", "dispatch");
        task.execute(first, this);
        if (received.size() != 1 || received.get(0) != first) {
            return "FAIL: task did not dispatch its action (received " + received.size() + ")";
        }

        boolean savedAutoMode = autoMode;
        try {
            autoMode = true;
            // 2. gated task is skipped during auto mode
            task.execute(new GeneralInformationEventF("self-test", "gated"), this);
            if (received.size() != 1) {
                return "FAIL: non-automode task ran during auto mode";
            }
            // 3. automode-enabled task runs during auto mode
            NotificationTaskF alwaysTask = new NotificationTaskF() {
                @Override
                public NotificationEventIDF getEventID() {
                    return NotificationEventIDF.EXCEPTION_CAUSED_FAILURE;
                }

                @Override
                protected boolean automodeEnabledTask() {
                    return true;
                }
            };
            alwaysTask.addNotificationAction(event -> {
                received.add(event);
                return true;
            });
            alwaysTask.execute(
                new GeneralFailureEventF("self-test automode-enabled dispatch"), this);
            if (received.size() != 2) {
                return "FAIL: automode-enabled task did not run during auto mode";
            }
        } finally {
            autoMode = savedAutoMode;
        }

        // 4. the default registry contains the five default tasks
        for (NotificationEventIDF id : List.of(NotificationEventIDF.PROOF_CLOSED,
            NotificationEventIDF.GENERAL_FAILURE, NotificationEventIDF.GENERAL_INFORMATION,
            NotificationEventIDF.TASK_ABANDONED, NotificationEventIDF.EXIT_KEY)) {
            if (!notificationTasks.containsKey(id)) {
                return "FAIL: default task for " + id + " missing";
            }
        }

        // 5. end-to-end dispatch through the registry (visible as toasts of both severities)
        handleNotificationEvent(new GeneralInformationEventF("Notification self-test",
            "framework dispatch works"));
        handleNotificationEvent(new GeneralFailureEventF(
            "Notification self-test: failure toast (expected)"));
        // unregistered id must be ignored silently (Swing parity: handleNotificationEvent)
        handleNotificationEvent(new AbandonTaskEventF());
        handleNotificationEvent(new ExitKeYEventF());
        LOGGER.info("Notification framework self-test dispatched all events");
        return "PASS";
    }

    /**
     * End-to-end self-test ({@code key.fx.verify.notifications}): fires each notification type
     * the way the app triggers them and asserts that the notification actions produce their
     * visible counterparts (toast / proof-closed dialog). Reports one {@code PASS} or
     * {@code FAIL} line per type.
     * <p>
     * The checks must run one {@link Platform#runLater(Runnable)} hop after each dispatch,
     * because the toast sink adds its toasts via {@code runLater} as well and {@code runLater}
     * tasks run in order — the hop after a dispatch therefore sees the toast. The assertion
     * thresholds are deltas over the toast count before the dispatch, so toasts fired by other
     * verifications do not falsify the result.
     *
     * @param proof the loaded proof used for the proof-closed notification (may be {@code null},
     *        the proof-closed fallback is exercised then)
     */
    public void verifyNotifications(Proof proof) {
        List<String> lines = new ArrayList<>();
        // 1. the framework semantics (task/action dispatch, auto-mode gating, default registry)
        lines.add("framework: " + verifyFramework());

        // 2. task-finished notification (Swing parity: WindowUserInterfaceControl
        // .taskFinishedInternal -> showNotification("Automated proof search", ...)); the task's
        // toast action must produce a visible toast
        int before = NotificationManagerF.getInstance().getVisibleToastCount();
        handleNotificationEvent(
            new GeneralInformationEventF("Automated proof search", "notification self-test"));
        Platform.runLater(() -> {
            lines.add("task-finished: " + (NotificationManagerF.getInstance()
                    .getVisibleToastCount() > before ? "PASS" : "FAIL: info toast not shown"));

            // 3. proof-closed notification (Swing parity: KeYMediator proofClosed listener ->
            // ProofClosedNotificationEvent -> ProofClosedJTextPaneDisplay); the dialog action
            // must open the statistics dialog (or, without a proof, the toast fallback)
            int beforeFallback = NotificationManagerF.getInstance().getVisibleToastCount();
            handleNotificationEvent(new ProofClosedNotificationEventF(proof));
            Platform.runLater(() -> {
                boolean dialog = ProofClosedDialogF.anyShowing();
                boolean fallbackToast =
                    NotificationManagerF.getInstance().getVisibleToastCount() > beforeFallback;
                lines.add("proof-closed: " + (dialog || fallbackToast ? "PASS"
                        : "FAIL: neither dialog nor fallback toast shown"));

                // 4. synthetic exception (Swing parity: ExceptionFailureEvent ->
                // ExceptionFailureNotificationDialog; registered by default since termmenu/S4 —
                // ExceptionFailureNotificationF is toast-only, see setDefaultNotifications —
                // so no add/remove dance needed; the assertion uses the toast-count delta)
                int beforeError = NotificationManagerF.getInstance().getVisibleToastCount();
                handleNotificationEvent(new ExceptionFailureEventF(
                    "Synthetic exception (notification self-test)",
                    new RuntimeException("notification self-test")));
                Platform.runLater(() -> {
                    lines.add("exception-failure: "
                        + (NotificationManagerF.getInstance().getVisibleToastCount() > beforeError
                                ? "PASS"
                                : "FAIL: error toast not shown"));
                    String report = String.join("\n", lines);
                    LOGGER.info("Notification verification report:\n{}", report);
                    boolean pass = report.lines().allMatch(line -> line.endsWith("PASS"));
                    // report visible like the other key.fx.verify.* self tests
                    NotificationManagerF.getInstance().notify("Notification verification: "
                        + (pass ? "PASS" : "FAIL") + " (" + report.replace("\n", "; ") + ")",
                        pass ? NotificationManagerF.Kind.INFO : NotificationManagerF.Kind.ERROR);
                });
            });
        });
    }

    /**
     * Listener section with inner classes used to receive KeY system events (Swing
     * {@code NotificationManager.NotificationListener}).
     */
    private class NotificationListenerF implements AutoModeListener {

        /**
         * auto mode started
         */
        @Override
        public void autoModeStarted(ProofEvent e) {
            autoMode = true;
        }

        /**
         * auto mode stopped
         */
        @Override
        public void autoModeStopped(ProofEvent e) {
            autoMode = false;
        }
    }
}
