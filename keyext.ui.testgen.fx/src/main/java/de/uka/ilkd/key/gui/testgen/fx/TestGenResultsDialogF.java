/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.testgen.fx;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;
import javafx.application.Platform;
import javafx.beans.property.ReadOnlyBooleanWrapper;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Button;
import javafx.scene.control.Dialog;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
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
 * The test-suite generation run dialog, FX port of {@code TGInfoDialog} (Swing
 * TGInfoDialog.java:22-144): a non-modal dialog streaming the generation log, with Start / Stop /
 * Close buttons and a list of the generated test files. The dialog's {@link LogSinkF} bridges the
 * {@code TestGenerationLifecycleListener} events (fired on the generation thread) to the FX
 * thread, mirroring {@code ThreadUtilities.invokeOnEventQueue} of the Swing original
 * (TGInfoDialog.java:73-82).
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing dialog embeds a live {@code TestgenOptionsPanel} on its
 * eastern edge (TGInfoDialog.java:126) so the options can be edited right before a run; the FX
 * port keeps the options exclusively in the Settings dialog (the global
 * {@link TestGenerationSettingsF} are re-read at run start). The "Close" button is disabled while
 * a run is active like in Swing (TGInfoDialog.java:118). The generated-files list is a simple
 * recursive listing of the configured output folder (the Swing dialog only prints "Writing test
 * file" into the log). The window may be {@code null} when the extension has not been connected
 * through the settings dialog yet (see {@link TestgenExtensionF}) — the dialog then starts with a
 * hint instead of a run; the owner stage is resolved from the clicked status-line control so the
 * dialog still opens properly owner-relative. The window is passed as a plain {@code Object}
 * because every {@code MainWindowF} type use in this module fails to compile (see
 * {@link TestgenReflectionF}).
 */
@NullMarked
final class TestGenResultsDialogF extends Dialog<Void> {

    private static final Logger LOGGER = LoggerFactory.getLogger(TestGenResultsDialogF.class);

    private final @Nullable Object window;
    private final TextArea log = new TextArea();
    private final ListView<String> generatedFiles = new ListView<>();
    private final ProgressIndicator progress = new ProgressIndicator();
    private final Label statusLabel = new Label("Idle");
    private final Button btnStart = new Button("Start");
    private final Button btnStop = new Button("Stop");
    private final Button btnClose = new Button("Close");
    private final ReadOnlyBooleanWrapper running = new ReadOnlyBooleanWrapper(this, "running");

    private TestGenerationTaskF runningTask;

    TestGenResultsDialogF(@Nullable Object window, @Nullable Stage owner) {
        this.window = window;
        setTitle("Test Suite Generation");
        if (owner != null) {
            initOwner(owner);
        }
        setResizable(true);

        progress.setVisible(false);
        HBox status = new HBox(8, progress, statusLabel);
        status.setAlignment(Pos.CENTER_LEFT);

        log.setEditable(false);
        log.setWrapText(true);
        log.setPromptText("Generation log");
        VBox.setVgrow(log, Priority.ALWAYS);

        Label filesHeader = new Label("Generated test files");
        VBox.setVgrow(generatedFiles, Priority.ALWAYS);

        VBox center = new VBox(6, status, log, filesHeader, generatedFiles);
        center.setPadding(new Insets(8));

        HBox buttons = new HBox(8, btnStart, btnStop, btnClose);
        buttons.setAlignment(Pos.CENTER_RIGHT);
        buttons.setPadding(new Insets(0, 8, 8, 8));

        BorderPane root = new BorderPane(center);
        root.setBottom(buttons);
        DialogPane pane = getDialogPane();
        pane.setPrefSize(900, 650);
        pane.setContent(root);

        btnStart.setOnAction(e -> startRun());
        btnStop.setOnAction(e -> requestStop());
        btnClose.setOnAction(e -> close());
        btnClose.setDefaultButton(true);
        btnStart.disableProperty().bind(running);
        btnStop.disableProperty().bind(running.not());
        btnClose.disableProperty().bind(running);
    }

    /** Shows the dialog non-modally (Swing {@code JDialog.setModal(false)}) and starts a run. */
    void showAndStart() {
        show();
        startRun();
    }

    /** The report sink of the run; the events fire on the generation thread. */
    private final LogSinkF logger = new LogSinkF() {
        @Override
        public void writeln(String message) {
            append(message + "\n");
        }

        @Override
        public void error(Throwable throwable) {
            // Swing TGInfoDialog.logger.writeException (TGInfoDialog.java:77-82).
            LOGGER.warn("Exception during test generation", throwable);
            append("Error: " + (throwable.getMessage() == null
                    ? throwable.getClass().getSimpleName()
                    : throwable.getMessage())
                + "\n");
        }

        @Override
        public void finished() {
            // Swing enables the exit button on finish (TGInfoDialog.java:90-92); the running flag
            // disables the whole button bar, so nothing further is needed here.
        }
    };

    private void startRun() {
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
        Object proof = TestgenReflectionF.proofOf(mediator);
        if (proof == null) {
            append("No proof is loaded — annotated/open goals for the generation are missing.\n");
            return;
        }
        Object ui = TestgenReflectionF.uiOf(captured);
        if (ui == null) {
            append("Cannot reach the proof environment — no UserInterfaceControl available.\n");
            return;
        }
        running.set(true);
        runningTask = null;
        statusLabel.setText("Generating test cases...");
        log.clear();
        generatedFiles.getItems().clear();

        TestGenerationTaskF task = new TestGenerationTaskF(ui, proof, logger);
        runningTask = task;
        task.setOnSucceeded(e -> {
            running.set(false);
            statusLabel.setText("Finished.");
            listGeneratedFiles();
        });
        task.setOnFailed(e -> {
            running.set(false);
            statusLabel.setText("Failed.");
            Throwable t = task.getException();
            append("Generation failed: " + (t == null ? "unknown error"
                    : t.getMessage() == null ? t.getClass().getSimpleName()
                            : t.getMessage())
                + "\n");
        });
        task.setOnCancelled(e -> {
            running.set(false);
            statusLabel.setText("Cancelled.");
            append("Test case generation cancelled.\n");
        });
        Thread thread = new Thread(task, "KeYTestGen");
        thread.setDaemon(true);
        thread.start();
    }

    private void requestStop() {
        TestGenerationTaskF task = runningTask;
        if (task != null) {
            append("Stopping test case generation.\n");
            task.requestStop();
        }
    }

    /**
     * Lists the generated files: a recursive scan of the configured output folder (the JUnit
     * tests are written to {@code <outputFolder>/src/test/java} by the {@code TestCaseGenerator},
     * TestCaseGenerator.java:306-311).
     */
    private void listGeneratedFiles() {
        Path root = Path.of(new TestGenerationSettingsF().outputFolderPath());
        List<String> files = new ArrayList<>();
        if (Files.isDirectory(root)) {
            try (Stream<Path> walk = Files.walk(root)) {
                walk.filter(p -> p.getFileName().toString().endsWith(".java")).sorted()
                        .map(p -> root.relativize(p).toString()).forEach(files::add);
            } catch (IOException e) {
                LOGGER.warn("Could not list generated test files in {}", root, e);
            }
        }
        if (files.isEmpty()) {
            files.add("(no test files found in " + root + ")");
        }
        generatedFiles.getItems().setAll(files);
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
