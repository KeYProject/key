/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanWrapper;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Dialog;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressIndicator;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The counterexample search dialog, FX counterpart of the Swing counterexample flow
 * ({@code CounterExampleAction.actionPerformed} + the {@code SolverListener} dialogs,
 * CounterExampleAction.java:105-120). Streams the search log into a {@link TextArea} with
 * Start / Stop / Close controls; the actual search runs off the FX thread in
 * {@link CounterExampleTaskF}.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing flow shows the counterexample model in the modal
 * {@code SolverListener} result dialogs; the FX port only prints the SMT statistics and the
 * outcome (found/not found) into the log. The auto-mode shell around the search
 * (CounterExampleAction.java:169-191) is dropped, like in {@link TestGenResultsDialogF}. The
 * window may be {@code null} when the extension has not been connected through the settings
 * dialog yet (see {@link TestgenExtensionF}) — the dialog then starts with a hint instead of a
 * search; the owner stage is resolved from the clicked status-line control.
 */
@NullMarked
final class CounterExampleResultsDialogF extends Dialog<Void> {

    private static final Logger LOGGER =
        LoggerFactory.getLogger(CounterExampleResultsDialogF.class);

    private final @Nullable Object window;
    private final TextArea log = new TextArea();
    private final ProgressIndicator progress = new ProgressIndicator();
    private final Label statusLabel = new Label("Idle");
    private final Button btnStart = new Button("Start");
    private final Button btnStop = new Button("Stop");
    private final Button btnClose = new Button("Close");
    private final ReadOnlyBooleanWrapper running = new ReadOnlyBooleanWrapper(this, "running");

    private CounterExampleTaskF runningTask;

    CounterExampleResultsDialogF(@Nullable Object window, @Nullable Stage owner) {
        this.window = window;
        setTitle("Counterexample Search");
        if (owner != null) {
            initOwner(owner);
        }
        setResizable(true);

        progress.setVisible(false);
        HBox status = new HBox(8, progress, statusLabel);
        status.setAlignment(Pos.CENTER_LEFT);

        log.setEditable(false);
        log.setWrapText(true);
        log.setPromptText("Search log");
        VBox.setVgrow(log, Priority.ALWAYS);

        VBox center = new VBox(6, status, log);
        center.setPadding(new Insets(8));

        HBox buttons = new HBox(8, btnStart, btnStop, btnClose);
        buttons.setAlignment(Pos.CENTER_RIGHT);
        buttons.setPadding(new Insets(0, 8, 8, 8));

        BorderPane root = new BorderPane(center);
        root.setBottom(buttons);
        DialogPane pane = getDialogPane();
        pane.setPrefSize(800, 500);
        pane.setContent(root);

        btnStart.setOnAction(e -> startSearch());
        btnStop.setOnAction(e -> requestStop());
        btnClose.setOnAction(e -> close());
        btnClose.setDefaultButton(true);
        btnStart.disableProperty().bind(running);
        btnStop.disableProperty().bind(running.not());
        btnClose.disableProperty().bind(running);
    }

    /** Shows the dialog non-modally and starts the counterexample search. */
    void showAndStart() {
        show();
        startSearch();
    }

    /** The report sink of the run; the events fire on the search thread. */
    private final LogSinkF logger = new LogSinkF() {
        @Override
        public void writeln(String message) {
            append(message + "\n");
        }

        @Override
        public void error(Throwable throwable) {
            LOGGER.warn("Exception during counterexample search", throwable);
            append("Error: " + (throwable.getMessage() == null
                    ? throwable.getClass().getSimpleName()
                    : throwable.getMessage())
                + "\n");
        }
    };

    private void startSearch() {
        if (running.get()) {
            return;
        }
        Object captured = window;
        if (captured == null) {
            append("The extension is not connected to a main window yet - open the "
                + "application settings (Options → Settings, section TestGen) once and the "
                + "next run will work.\n");
            // KNOWN-SIMPLIFIED: the frozen FX SPI passes the window only to the settings
            // panel (TestgenExtensionF); until then the run is validated on click.
            return;
        }
        Object mediator = TestgenReflectionF.mediatorOf(captured);
        Object goal = TestgenReflectionF.goalOf(mediator);
        if (goal == null) {
            append("No open goal is selected — cannot search for a counterexample.\n");
            return;
        }
        Object proof = TestgenReflectionF.proofOfGoal(goal);
        Object sequent = TestgenReflectionF.sequentOfGoal(goal);
        Object ui = TestgenReflectionF.uiOf(captured);
        if (proof == null || sequent == null || ui == null) {
            append("Cannot reach the proof environment — the search could not be started.\n");
            return;
        }
        running.set(true);
        runningTask = null;
        statusLabel.setText("Searching for counterexamples...");
        log.clear();

        CounterExampleTaskF task = new CounterExampleTaskF(ui, proof, sequent, logger);
        runningTask = task;
        task.setOnSucceeded(e -> {
            running.set(false);
            statusLabel.setText("Finished.");
        });
        task.setOnFailed(e -> {
            running.set(false);
            statusLabel.setText("Failed.");
            Throwable t = task.getException();
            append("Counterexample search failed: " + (t == null ? "unknown error"
                    : t.getMessage() == null ? t.getClass().getSimpleName()
                            : t.getMessage())
                + "\n");
        });
        task.setOnCancelled(e -> {
            running.set(false);
            statusLabel.setText("Cancelled.");
            append("Counterexample search cancelled.\n");
        });
        Thread thread = new Thread(task, "KeYCounterExample");
        thread.setDaemon(true);
        thread.start();
    }

    private void requestStop() {
        CounterExampleTaskF task = runningTask;
        if (task != null) {
            append("Stopping counterexample search.\n");
            task.requestStop();
        }
    }

    /** Appends a log line, marshalled to the FX thread (the events fire on the worker thread). */
    private void append(String text) {
        if (Platform.isFxApplicationThread()) {
            log.appendText(text);
        } else {
            Platform.runLater(() -> log.appendText(text));
        }
    }
}
