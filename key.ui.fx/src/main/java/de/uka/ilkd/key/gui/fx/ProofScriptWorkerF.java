/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.net.URI;
import javafx.application.Platform;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.TextArea;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptException;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * P3b/B12: executes a proof script on the current proof, the JavaFX counter-part of the Swing
 * {@code ProofScriptWorker} (ProofScriptWorker.java). Deliberate port differences:
 * <ul>
 * <li>the log window is a JavaFX {@link Stage} (no FXML) with a non-editable monospace
 * {@link TextArea} and a Stop button that interrupts the worker {@link Thread}
 * (Swing: {@code JDialog} + {@code SwingWorker.cancel(true)}; Swing's {@code InterruptListener}
 * is key.ui-only and not portable);</li>
 * <li>the script runs on a plain background thread (Swing {@code SwingWorker.doInBackground}),
 * the engine's command monitor appends to the log on the FX thread via {@link Platform#runLater};
 * </li>
 * <li>failures and interruptions are reported as notification toasts (Swing
 * {@code IssueDialog.showExceptionDialog} for arbitrary {@code done()} failures); the interrupted
 * case ends silently like Swing ({@code ProofScriptWorker.doInBackground}, ProofScriptWorker.java
 * :90-92).</li>
 * </ul>
 * The script itself is executed by the core {@link ProofScriptEngine} with the window's
 * {@link AbstractUserInterfaceControl} (the {@link WindowUserInterfaceControlF}), so the prover
 * callbacks and task observers of the commands reach the FX UI exactly like interactive runs.
 */
public final class ProofScriptWorkerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptWorkerF.class);

    private final KeYMediatorF mediator;
    private final AbstractUserInterfaceControl ui;
    private final KeyAst.ProofScript script;

    /**
     * the initially selected goal, may be {@code null} (then the engine picks the first open
     * automatic goal).
     */
    private final @Nullable Goal initiallySelectedGoal;

    /** owner of the log window, may be {@code null} (headless usage). */
    private final @Nullable Window owner;

    private @Nullable ProofScriptEngine engine;
    private @Nullable Thread workerThread;
    private @Nullable Stage monitor;
    private @Nullable TextArea logArea;

    /**
     * Creates the worker.
     *
     * @param mediator the mediator (selection, proof lookup)
     * @param ui the user interface control fed to the script engine ({@code
     *        WindowUserInterfaceControlF})
     * @param script the parsed script
     * @param initiallySelectedGoal the goal the script starts at, or {@code null}
     * @param owner the owner window of the log dialog, or {@code null}
     */
    public ProofScriptWorkerF(KeYMediatorF mediator, AbstractUserInterfaceControl ui,
            KeyAst.ProofScript script, @Nullable Goal initiallySelectedGoal,
            @Nullable Window owner) {
        this.mediator = mediator;
        this.ui = ui;
        this.script = script;
        this.initiallySelectedGoal = initiallySelectedGoal;
        this.owner = owner;
    }

    /**
     * Starts the script (Swing {@code ProofScriptWorker.init()} + {@code execute()}): opens the
     * non-modal log window and launches the background script thread. Must be called on the FX
     * thread (the monitor is a JavaFX stage). Without a selected (or initially-selected) proof
     * nothing is started.
     */
    public void start() {
        Proof proof = initiallySelectedGoal != null ? initiallySelectedGoal.proof()
                : mediator.getSelectedProof();
        if (proof == null) {
            LOGGER.warn("Proof script: no proof selected, not started");
            return;
        }
        showMonitor(proof);
        workerThread = new Thread(() -> runScript(proof), "fx-proof-script");
        workerThread.start();
    }

    /**
     * Opens the log window (Swing {@code ProofScriptWorker.makeDialog}, ProofScriptWorker.java
     * :96-112).
     */
    private void showMonitor(Proof proof) {
        URI uri = script.getStartLocation().getFileURI().orElse(null);
        TextArea log = new TextArea("Running script from URL '" + uri + "':\n");
        log.setEditable(false);
        log.setStyle("-fx-font-family: monospace;");
        VBox.setVgrow(log, Priority.ALWAYS);
        Button cancelButton = new Button("Stop");
        cancelButton.setOnAction(e -> {
            Thread t = workerThread;
            if (t != null) {
                t.interrupt();
            }
        });
        VBox box = new VBox(8, log, cancelButton);
        Stage stage = new Stage();
        stage.initOwner(owner);
        stage.initModality(Modality.NONE);
        stage.setTitle("Running Script ...");
        stage.setScene(new Scene(box, 750, 400));
        stage.show();
        this.monitor = stage;
        this.logArea = log;
    }

    /**
     * The script thread (Swing {@code ProofScriptWorker.doInBackground}, ProofScriptWorker.java
     * :84-94).
     */
    private void runScript(Proof proof) {
        try {
            ProofScriptEngine engine = new ProofScriptEngine(proof);
            this.engine = engine;
            engine.setInitiallySelectedGoal(initiallySelectedGoal);
            engine.setCommandMonitor(msg -> Platform.runLater(() -> appendLog(msg)));
            engine.execute(ui, script);
            Platform.runLater(() -> finish(proof, null));
        } catch (InterruptedException ex) {
            LOGGER.debug("Proof script has been interrupted:", ex);
            Platform.runLater(() -> finish(proof, "interrupted."));
        } catch (ScriptException ex) {
            LOGGER.error("", ex);
            Platform.runLater(() -> finish(proof, "failed: " + ex.getMessage()));
        } catch (RuntimeException ex) {
            LOGGER.error("", ex);
            Platform.runLater(() -> finish(proof, "failed: " + ex.getMessage()));
        }
    }

    /**
     * Closes the log window and, unless the run completed cleanly, reports the interruption or
     * failure as a warning toast (the success path shows no notification — the proof tree /
     * sequent views already react to the applied rules; Swing shows its TaskFinishedNotifications
     * via the macros).
     */
    private void finish(Proof proof, @Nullable String warning) {
        if (monitor != null) {
            monitor.close();
        }
        if (warning != null) {
            NotificationManagerF.getInstance()
                    .notify("Proof script " + warning, Kind.WARNING);
        }
        selectGoalOrNode(proof);
    }

    /**
     * Appends one engine message to the log (Swing {@code ProofScriptWorker.process},
     * ProofScriptWorker.java:115-139).
     */
    private void appendLog(ProofScriptEngine.Message info) {
        TextArea log = logArea;
        if (log == null) {
            return;
        }
        StringBuilder message = new StringBuilder("\n---\n");
        if (info instanceof ProofScriptEngine.EchoMessage(String msg)) {
            message.append(msg);
        } else {
            var exec = (ProofScriptEngine.ExecuteInfo) info;
            if (exec.command().startsWith("'echo ")) {
                return;
            }
            exec.location().getFileURI().ifPresent(uri -> message.append(uri).append(":"));
            message.append(exec.location().getPosition().line())
                    .append(": Executing on goal ").append(exec.nodeSerial()).append('\n')
                    .append(exec.command());
        }
        log.appendText(message.toString());
    }

    /**
     * Selects the first open automatic goal of the script run, or the default selection when the
     * proof is closed or the state map is unavailable (Swing {@code
     * ProofScriptWorker.selectGoalOrNode}, ProofScriptWorker.java:176-191).
     */
    private void selectGoalOrNode(Proof proof) {
        KeYSelectionModel selectionModel = mediator.getSelectionModel();
        ProofScriptEngine engine = this.engine;
        if (engine != null && !proof.closed()) {
            try {
                selectionModel.setSelectedGoal(engine.getStateMap().getFirstOpenAutomaticGoal());
                return;
            } catch (ScriptException e) {
                LOGGER.warn("Script threw exception", e);
            } catch (RuntimeException e) {
                LOGGER.warn("Unexpected exception", e);
            }
        }
        mediator.defaultSelection();
    }
}
