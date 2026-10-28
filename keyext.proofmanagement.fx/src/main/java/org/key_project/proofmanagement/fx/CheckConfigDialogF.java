/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.proofmanagement.fx;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Dialog;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.help.HelpFacadeF;

import org.key_project.proofmanagement.Main;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The check-configuration dialog of the proof management extension, JavaFX port of the Swing
 * {@code org.key_project.proofmanagement.CheckConfigDialog} (Swing CheckConfigDialog.java:26-299).
 * Selects the active checkers (Missing Proofs / Settings / Replay / Dependency), the proof bundle
 * to check and the optional HTML report location, then runs the checkers in the background.
 * <p>
 * Port notes and deviations from the Swing original:
 * <ul>
 * <li>The checkers themselves are <em>reused unchanged</em>: the dialog drives
 * {@link Main.CheckCommand} exactly like the Swing worker (CheckConfigDialog.java:44-86) — this
 * keeps the report generation and the per-checker orchestration identical.</li>
 * <li><b>KNOWN-SIMPLIFIED:</b> the Swing {@code BlockingGlassPane} (CheckConfigDialog.java:40,
 * 96-173) is replaced by explicitly disabling the input controls while the check runs; the "Run
 * checkers" button turns into "Stop" and stays the only enabled control, mirroring the glass
 * pane's Stop-only pass-through. Like the Swing original, cancelling may leave partial output on
 * disk (the checkers do not abort their loops on interruption).</li>
 * <li><b>KNOWN-SIMPLIFIED:</b> the Swing bundle/report choosers use the AWT {@code
 * KeYFileChooser} with the {@code PROOF_BUNDLE_FILTER} (.zproof) and {@code
 * PROOF_MANAGEMENT_REPORT_FILTER} (.html) filters (CheckConfigDialog.java:213-256); the FX port
 * uses {@link FileChooser} with equivalent extension filters. File-only selection matches the
 * Swing dialog (the original also only selects files, even though directory bundles exist).</li>
 * <li><b>KNOWN-SIMPLIFIED:</b> the Swing worker opens the generated report via
 * {@code Desktop.getDesktop().open} (CheckConfigDialog.java:66-69); the FX port (no AWT/Swing)
 * opens it through the {@link HelpFacadeF} browser seam (host services with a desktop fallback),
 * i.e. {@code HelpFacadeF.openExternal(reportPath.toUri().toString())}.</li>
 * <li>The Swing dialog leaves no trace of the check outcome on success besides the opened report
 * and the stdout log; the FX port additionally reports the outcome in a small result
 * {@link Alert} (requested by the MP9.6 port) before closing the dialog.</li>
 * </ul>
 */
@NullMarked
class CheckConfigDialogF extends Dialog<Void> {
    private static final Logger LOGGER = LoggerFactory.getLogger(CheckConfigDialogF.class);

    /**
     * All checkers and the report generation are selected by default (Swing
     * CheckConfigDialog.java:187-191).
     */
    private final CheckBox missingProofsCheck = new CheckBox("Missing Proofs Checker");
    private final CheckBox settingsCheck = new CheckBox("Settings Checker");
    private final CheckBox replayCheck = new CheckBox("Replay Checker");
    private final CheckBox dependencyCheck = new CheckBox("Dependency Checker");
    private final CheckBox reportCheck = new CheckBox("Generate Report");

    private final TextField bundleFileField = new TextField();
    private final TextField reportFileField = new TextField();

    private final Button chooseBundleButton = new Button("Choose file...");
    private final Button chooseReportButton = new Button("Choose report location...");
    private final Button runButton = new Button("Run checkers");
    private final Button cancelButton = new Button("Cancel");

    private Task<Integer> checkWorker;

    CheckConfigDialogF(@Nullable Window owner) {
        setTitle("Check configuration");
        setResizable(true);
        if (owner != null) {
            initOwner(owner);
        }

        // all checkers and the report are active by default (Swing CheckConfigDialog.java:187-191)
        missingProofsCheck.setSelected(true);
        settingsCheck.setSelected(true);
        replayCheck.setSelected(true);
        dependencyCheck.setSelected(true);
        reportCheck.setSelected(true);

        bundleFileField.setEditable(false);
        bundleFileField.setPromptText("No proof bundle selected");
        reportFileField.setEditable(false);
        reportFileField.setPromptText("Choose the location or file for the HTML report "
            + "(default file name: \"report.html\")");

        chooseBundleButton.setOnAction(e -> chooseBundle());
        chooseReportButton.setOnAction(e -> chooseReportLocation());
        // the report controls are enabled only while the report is selected (Swing
        // CheckConfigDialog.java:239-247)
        reportCheck.selectedProperty().addListener(
            (obs, old, selected) -> {
                chooseReportButton.setDisable(!selected);
                reportFileField.setDisable(!selected);
            });
        runButton.setOnAction(e -> runCheckers());
        cancelButton.setOnAction(e -> hide());

        getDialogPane().setContent(buildContent());
    }

    /** Builds the dialog content: the three titled sections plus the button row. */
    private VBox buildContent() {
        VBox checkers = new VBox(6, missingProofsCheck, settingsCheck, replayCheck,
            dependencyCheck);
        TitledPane checkersPane = new TitledPane("Available Checkers", checkers);
        checkersPane.setCollapsible(false);

        HBox bundleBox = new HBox(6, bundleFileField, chooseBundleButton);
        HBox.setHgrow(bundleFileField, Priority.ALWAYS);
        TitledPane bundlePane = new TitledPane("Proof bundle to check", bundleBox);
        bundlePane.setCollapsible(false);

        HBox reportBox = new HBox(6, reportFileField, chooseReportButton);
        HBox.setHgrow(reportFileField, Priority.ALWAYS);
        VBox reportInner = new VBox(6, reportCheck, reportBox);
        TitledPane reportPane = new TitledPane("HTML report", reportInner);
        reportPane.setCollapsible(false);

        HBox buttons = new HBox(10, runButton, cancelButton);
        buttons.setAlignment(Pos.BOTTOM_RIGHT);

        VBox content = new VBox(10, checkersPane, bundlePane, reportPane, buttons);
        content.setPadding(new Insets(12));
        return content;
    }

    /** File chooser for a proof bundle file, mirroring the Swing {@code PROOF_BUNDLE_FILTER}. */
    private void chooseBundle() {
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Choose file");
        chooser.getExtensionFilters()
                .add(new FileChooser.ExtensionFilter("proof bundles (.zproof)", "*.zproof"));
        var file = chooser.showOpenDialog(getDialogPane().getScene().getWindow());
        if (file != null) {
            bundleFileField.setText(file.toString());
        }
    }

    /** File chooser for the HTML report location (Swing {@code PROOF_MANAGEMENT_REPORT_FILTER}). */
    private void chooseReportLocation() {
        FileChooser chooser = new FileChooser();
        chooser.setTitle("Choose file or directory");
        chooser.getExtensionFilters()
                .add(new FileChooser.ExtensionFilter("proof management reports (.html)",
                    "*.html"));
        var file = chooser.showOpenDialog(getDialogPane().getScene().getWindow());
        if (file != null) {
            reportFileField.setText(file.toString());
        }
    }

    /**
     * Runs the selected checkers on the chosen bundle in a background {@link Task} (Swing
     * {@code ProofManagementCheckWorker}, CheckConfigDialog.java:44-86); on success the dialog
     * closes and a small result alert reports the outcome.
     */
    private void runCheckers() {
        if (bundleFileField.getText().isEmpty()) {
            showAlert(Alert.AlertType.ERROR, "Error", null,
                "Please choose a proof bundle to check!");
            return;
        }

        // lock the dialog while the check runs; the "Run checkers" button becomes "Stop" and
        // stays the only enabled control (Swing BlockingGlassPane, CheckConfigDialog.java:40,
        // 96-173)
        setRunning(true);
        checkWorker = new Task<>() {
            @Override
            protected Integer call() throws Exception {
                Path reportPath = null;
                if (reportCheck.isSelected()) {
                    reportPath = Paths.get(reportFileField.getText());
                    if (Files.isDirectory(reportPath)) {
                        // add default name (Swing CheckConfigDialog.java:50-53)
                        reportPath = reportPath.resolve("report.html");
                    }
                }
                Main.CheckCommand c = new Main.CheckCommand();
                c.missing = missingProofsCheck.isSelected();
                c.settings = settingsCheck.isSelected();
                c.replay = replayCheck.isSelected();
                c.dependency = dependencyCheck.isSelected();
                c.bundlePath = Paths.get(bundleFileField.getText());
                c.reportPath = reportPath;
                int exitCode = c.call();
                if (reportPath != null) {
                    // open the report in the system browser (Swing
                    // CheckConfigDialog.java:66-69 via java.awt.Desktop; the FX port uses the
                    // HelpFacadeF browser seam — KNOWN-SIMPLIFIED, see class javadoc)
                    HelpFacadeF.openExternal(reportPath.toUri().toString());
                }
                return exitCode;
            }
        };
        checkWorker.setOnSucceeded(e -> {
            int exitCode = checkWorker.getValue();
            setRunning(false);
            hide();
            showResultAlert(exitCode);
        });
        checkWorker.setOnCancelled(e -> {
            LOGGER.info("ProofManagement was cancelled by the user!");
            setRunning(false);
        });
        checkWorker.setOnFailed(e -> {
            Throwable error = checkWorker.getException();
            LOGGER.error("ProofManagement check failed", error);
            setRunning(false);
            showAlert(Alert.AlertType.ERROR, "Error", "ProofManagement interrupted due to "
                + "critical error.", String.valueOf(error));
        });
        Thread thread = new Thread(checkWorker, "proof-management-check");
        thread.setDaemon(true);
        thread.start();
    }

    /** Small result alert reporting the outcome of the finished check run. */
    private void showResultAlert(int exitCode) {
        StringBuilder details = new StringBuilder();
        details.append("The selected checkers have been executed on the proof bundle.")
                .append(System.lineSeparator()).append(System.lineSeparator())
                .append("Exit code: ").append(exitCode)
                .append(exitCode == 0 ? " (success)" : " (error)");
        if (reportCheck.isSelected()) {
            Path reportPath = Paths.get(reportFileField.getText());
            if (Files.isDirectory(reportPath)) {
                reportPath = reportPath.resolve("report.html");
            }
            details.append(System.lineSeparator())
                    .append("HTML report: ").append(reportPath)
                    .append(" (opened in the system browser)");
        }
        details.append(System.lineSeparator()).append(System.lineSeparator())
                .append("Detailed messages are written to the log.");
        showAlert(Alert.AlertType.INFORMATION, "Check finished", "Proof management check done.",
            details.toString());
    }

    /**
     * Toggles the running state: while running, all inputs except the "Stop" button are disabled
     * and the dialog cannot be closed by the user (Swing {@code BlockingGlassPane} +
     * {@code DO_NOTHING_ON_CLOSE}, CheckConfigDialog.java:273-277).
     *
     * @param running whether the check task is running
     */
    private void setRunning(boolean running) {
        missingProofsCheck.setDisable(running);
        settingsCheck.setDisable(running);
        replayCheck.setDisable(running);
        dependencyCheck.setDisable(running);
        reportCheck.setDisable(running);
        bundleFileField.setDisable(running);
        reportFileField.setDisable(running);
        chooseBundleButton.setDisable(running);
        chooseReportButton.setDisable(running);
        cancelButton.setDisable(running);
        runButton.setText(running ? "Stop" : "Run checkers");
        setOnCloseRequest(running ? e -> e.consume() : null);
        if (running) {
            runButton.setOnAction(e -> {
                if (checkWorker != null) {
                    checkWorker.cancel(true);
                }
            });
        } else {
            runButton.setOnAction(e -> runCheckers());
        }
    }

    /** Small modal alert helper (headless-safe: only called on user interaction). */
    private static void showAlert(Alert.AlertType type, String title, @Nullable String header,
            String message) {
        Alert alert = new Alert(type);
        alert.setTitle(title);
        alert.setHeaderText(header);
        alert.setContentText(message);
        alert.showAndWait();
    }
}
