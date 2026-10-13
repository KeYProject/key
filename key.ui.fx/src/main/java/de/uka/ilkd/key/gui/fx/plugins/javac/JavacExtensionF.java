/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.plugins.javac;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.CompletableFuture;
import javafx.application.Platform;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.Control;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.gui.fx.IssueDialogF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.fonticons.MaterialDesignRegular;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The Java Compiler Check extension, FX port of {@code JavacExtension} (Swing {@code
 * key.ui/plugins/javac/JavacExtension.java}): checks the loaded Java files for problems with
 * Javac and reports the diagnostics in a status-line button ({@link #getStatusLineControls()})
 * that opens the full issue list on click; the options live in the settings dialog ({@link
 * JavacSettingsProviderF}, already ported).
 *
 * <p>
 * Swing runs the compiler asynchronously ({@code JavaCompilerCheckFacade.check*} returns a
 * {@link CompletableFuture}) but then blocks the UI thread with {@code get()} — the FX port only
 * forwards the completion to the FX thread instead.
 */
@KeYGuiExtensionF.Info(name = "Java Compiler Check", optional = true,
    description = "Checks the loaded Java files for problems with Javac",
    experimental = false)
public class JavacExtensionF implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF,
        KeYGuiExtensionF.StartupF, KeYSelectionListener {

    /**
     * Color used for the icon if javac didn't produce any diagnostics (Swing {@code COLOR_FINE}).
     */
    private static final String COLOR_FINE = "#5078c8";

    /**
     * Color used if javac reported errors (Swing {@code COLOR_ERROR}).
     */
    private static final String COLOR_ERROR = "#c81450";

    /**
     * Color used if javac only reported warnings (Swing {@code COLOR_WARN}).
     */
    private static final String COLOR_WARN = "#c87850";

    private static final Logger LOGGER = LoggerFactory.getLogger(JavacExtensionF.class);

    /**
     * The button added to the status line (Swing uses a {@code JButton} as well).
     */
    private final Button lblStatus = new Button("Javac");

    private KeYMediatorF mediator;

    /** Prevents a concurrent re-run of the compiler check for the same proof. */
    private Proof checkRunningFor;

    /**
     * Initialize the extension. Adds interactivity to the {@link #lblStatus} (Swing constructor,
     * JavacExtension.java:98-124).
     */
    public JavacExtensionF() {
        lblStatus.setTooltip(new Tooltip("Check the loaded Java files with javac"));
        lblStatus.setDisable(true);
        lblStatus.setOnAction(ev -> {
            Proof proof = mediator != null ? mediator.getSelectedProof() : null;
            if (proof == null) {
                return;
            }
            try {
                JavacData data = JavacData.of(proof);
                MainWindowF window = MainWindowF.getInstance();
                javafx.stage.Window owner = window != null ? window.getStage() : null;
                if (data.nonJavaProof) {
                    information(owner, "The current proof contains no Java model.");
                    return;
                }
                if (data.issues.isEmpty()) {
                    information(owner, "No Javac issues found.");
                    return;
                }
                IssueDialogF.showIssuesDialog(owner, "Java Compiler Diagnostics",
                    "The Java compiler issued these diagnostics for your source code:",
                    entries(data.issues));
            } catch (IllegalStateException e) {
                LOGGER.info("No Javac information available for current proof.");
            }
        });
    }

    @Override
    public List<Control> getStatusLineControls() {
        return List.of(lblStatus);
    }

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        this.mediator = mediator;
        mediator.getSelectionModel().addKeYSelectionListener(this);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<de.uka.ilkd.key.proof.Node> e) {
        /* ignored */
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        loadProof(e.getSource().getSelectedProof());
    }

    /**
     * Runs (or re-reads) the javac check of the given proof (Swing {@code loadProof},
     * JavacExtension.java:126-176): the diagnostics are computed once per proof and cached in the
     * proof's user data; the status button reflects the progress and the result.
     */
    private void loadProof(Proof selectedProof) {
        try {
            updateLabel(selectedProof != null ? JavacData.of(selectedProof) : null);
        } catch (IllegalStateException e) {
            if (selectedProof == null) {
                return;
            }
            JavacData data = new JavacData();
            selectedProof.getUserData().register(data);
            final JavaModel jm = selectedProof.getServices().getJavaModel();

            if (jm == JavaModel.NO_MODEL) {
                data.nonJavaProof = true;
                updateLabel(data);
                return;
            }

            Path bootClassPath = jm.getBootClassPath() != null ? jm.getBootClassPath() : null;
            List<Path> classpath = jm.getClassPath();
            Path javaPath = jm.getModelDir();

            lblStatus.setText("Javac runs");
            setIcon(MaterialDesignRegular.WATCH, null);
            if (checkRunningFor == selectedProof) {
                return; // a selection event for a proof whose check is still running
            }
            checkRunningFor = selectedProof;

            var settings = JavacSettingsProviderF.getJavacSettings();
            CompletableFuture<List<PositionedIssueStringF>> task =
                settings.getUseProcessors()
                        ? JavaCompilerCheckFacadeF.checkExternally(bootClassPath, classpath,
                            javaPath,
                            settings)
                        : JavaCompilerCheckFacadeF.check(bootClassPath, classpath, javaPath,
                            settings);
            task.thenAccept(it -> Platform.runLater(() -> {
                lblStatus.setText("Javac finished");
                data.issues = it;
                checkRunningFor = null;
                updateLabel(data);
            }));
        }
    }

    /**
     * Set the button text, icon and enabled status based on the provided data (Swing {@code
     * updateLabel}, JavacExtension.java:181-218).
     *
     * @param data data to use
     */
    private void updateLabel(JavacData data) {
        if (data == null || data.issues == null) {
            lblStatus.setText("Javac");
            setIcon(null, null);
            lblStatus.setDisable(true);
            return;
        }
        lblStatus.setDisable(false);
        if (data.nonJavaProof) {
            lblStatus.setText("No Java");
            setIcon(null, null);
            return;
        }

        lblStatus.setText("Javac (" + data.issues.size() + ")");
        if (data.issues.isEmpty()) {
            setIcon(MaterialDesignRegular.CHECK_BOX, COLOR_FINE);
        } else {
            boolean onlyWarnings = data.issues.stream()
                    .allMatch(it -> it.getKind() != PositionedIssueStringF.Kind.ERROR);
            if (onlyWarnings) {
                setIcon(MaterialDesignRegular.WARNING, COLOR_WARN);
            } else {
                setIcon(MaterialDesignRegular.ERROR_OUTLINE, COLOR_ERROR);
            }
        }
    }

    /**
     * Sets the status button's icon glyph with the given fill color (Swing colors the icon via
     * the {@code ColorSettings} values); {@code null} removes the graphic.
     */
    private void setIcon(MaterialDesignRegular glyph, String fill) {
        if (glyph == null) {
            lblStatus.setGraphic(null);
            return;
        }
        javafx.scene.Node icon = IconFactoryF.createIcon(glyph, 16);
        if (fill != null) {
            icon.setStyle("-fx-fill: " + fill + ";");
        }
        lblStatus.setGraphic(icon);
    }

    /**
     * converts the diagnostics into the issue dialog entries, sorted by their location (Swing
     * passes a {@code TreeSet} of the comparable {@code PositionedIssueStringF}s).
     */
    private static List<IssueDialogF.IssueEntry> entries(List<PositionedIssueStringF> issues) {
        List<IssueDialogF.IssueEntry> entries = new ArrayList<>();
        for (PositionedIssueStringF issue : new TreeSet<>(issues)) {
            IssueDialogF.Kind kind = issue.getKind() == PositionedIssueStringF.Kind.ERROR
                    ? IssueDialogF.Kind.ERROR
                    : IssueDialogF.Kind.WARNING;
            entries.add(new IssueDialogF.IssueEntry(issue, "", kind));
        }
        return entries;
    }

    /** Swing {@code JOptionPane.showMessageDialog} parity. */
    private static void information(javafx.stage.Window owner, String message) {
        Alert alert = new Alert(Alert.AlertType.INFORMATION, message);
        alert.setTitle("Message");
        alert.setHeaderText(null);
        if (owner != null) {
            alert.initOwner(owner);
        }
        alert.showAndWait();
    }
}
