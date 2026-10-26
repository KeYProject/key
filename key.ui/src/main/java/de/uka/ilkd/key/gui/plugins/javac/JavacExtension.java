/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.javac;

import java.awt.*;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.PositionedIssueString;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.MaterialDesignRegular;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension provides Javac checks for recent-loaded Java files.
 * <p>
 * Provides an entry in the status line for access.
 *
 * @author Alexander Weigl
 * @version 1 (18.12.22)
 * @see JavaCompilerCheckFacade
 */
@KeYGuiExtension.Info(name = "Java Compiler Check", optional = true,
    description = "Checks the loaded Java files for problems with Javac",
    experimental = false)
@NullMarked
public class JavacExtension
        implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup,
        KeYSelectionListener, KeYGuiExtension.Settings {
    /**
     * Color used for the label if javac didn't produce any diagnostics.
     */
    private static final ColorSettings.ColorProperty COLOR_FINE =
        ColorSettings.define("javac.fine", "",
            new Color(80, 120, 200));
    /**
     * Color used if javac reported errors.
     */
    private static final ColorSettings.ColorProperty COLOR_ERROR =
        ColorSettings.define("javac.error", "",
            new Color(200, 20, 80));
    /**
     * Color used if javac only reported warnings.
     */
    private static final ColorSettings.ColorProperty COLOR_WARN =
        ColorSettings.define("javac.warn", "",
            new Color(200, 120, 80));
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(JavacExtension.class);

    /**
     * Icon used when no diagnostics were produced.
     */
    public static final IconFontProvider ICON_CHECK =
        new IconFontProvider(MaterialDesignRegular.CHECK_BOX, COLOR_FINE.get());

    /**
     * Icon used when only warnings were emitted.
     */
    public static final IconFontProvider ICON_WARN =
        new IconFontProvider(MaterialDesignRegular.WARNING, COLOR_WARN.get());
    /**
     * Icon used when errors were reported by javac.
     */
    public static final IconFontProvider ICON_ERROR =
        new IconFontProvider(MaterialDesignRegular.ERROR_OUTLINE, COLOR_ERROR.get());
    /**
     * Icon used whilst the code is compiling.
     */
    public static final IconFontProvider ICON_WAIT =
        new IconFontProvider(MaterialDesignRegular.WATCH);

    /**
     * The button added to the status line.
     */
    private final JButton lblStatus = new JButton("Javac");

    private @Nullable KeYMediator mediator;

    /**
     * Initialize the extension. Adds interactivity to the {@link #lblStatus}.
     */
    public JavacExtension() {
        lblStatus.addActionListener(ev -> {
            KeYMediator currentMediator = mediator;
            if (currentMediator != null) {
                Proof selectedProof = currentMediator.getSelectedProof();
                if (selectedProof != null) {
                    try {
                        JavacData data = selectedProof.getUserData().get(JavacData.class);
                        List<PositionedIssueString> issues = data.issues;
                        if (data.nonJavaProof) {
                            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                                "The current proof contains no Java model.");
                            return;
                        }
                        if (issues == null || issues.isEmpty()) {
                            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                                "No Javac issues found.");
                            return;
                        }
                        IssueDialog is =
                            new IssueDialog(MainWindow.getInstance(), "Java Compiler Diagnostics",
                                "The Java compiler issued these diagnostics for your source code:",
                                new TreeSet<>(issues));
                        is.setVisible(true);
                    } catch (IllegalStateException e) {
                        LOGGER.info("No Javac information available for current proof.");
                    }
                }
            }
        });
    }

    private void loadProof(@Nullable Proof selectedProof) throws RuntimeException {
        if (selectedProof == null) {
            updateLabel(null);
            return;
        }
        try {
            JavacData data = selectedProof.getUserData().get(JavacData.class);
            updateLabel(data);
        } catch (IllegalStateException e) {
            JavacData data = new JavacData();
            selectedProof.getUserData().register(data);
            final JavaModel jm = selectedProof.getServices().getJavaModel();

            if (jm == null || jm == JavaModel.NO_MODEL) {
                data.nonJavaProof = true;
                updateLabel(data);
                return;
            }

            Path bootClassPath = jm.getBootClassPath();
            List<Path> classpath = jm.getClassPath();
            if (classpath == null) {
                // a Java model always provides a (possibly empty) class path
                throw new NullPointerException("No class path available.");
            }
            Path javaPath = jm.getModelDir();
            if (javaPath == null) {
                // a Java model always refers to the directory of its sources
                throw new NullPointerException("No model directory available.");
            }

            lblStatus.setForeground(Color.black);
            lblStatus.setText("Javac runs");
            lblStatus.setIcon(ICON_WAIT.get(16));

            JavacSettings settings = JavacSettingsProvider.getJavacSettings();
            CompletableFuture<List<PositionedIssueString>> task = settings.getUseProcessors()
                    ? JavaCompilerCheckFacade.checkExternally(bootClassPath,
                        classpath,
                        javaPath,
                        settings)
                    : JavaCompilerCheckFacade.check(bootClassPath, classpath,
                        javaPath, settings);
            try {
                task.thenAccept(it -> SwingUtilities.invokeLater(() -> {
                    lblStatus.setText("Javac finished");
                    data.issues = it;
                    updateLabel(data);
                })).get();
            } catch (InterruptedException | ExecutionException ex) {
                throw new RuntimeException(ex);
            }
        }
    }

    /**
     * Set the label text, icon and enabled status based on the provided data.
     *
     * <p>
     * Clearing the status icon is expressed as setting the label's icon to {@code null}; the
     * swing model declares a non-null icon parameter while the implementation accepts {@code null}
     * to clear the icon, suppressed with a scoped key.
     *
     * @param data data to use
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private void updateLabel(@Nullable JavacData data) {
        if (data == null || data.issues == null) {
            lblStatus.setText("Javac");
            lblStatus.setIcon((Icon) null);
            lblStatus.setForeground(Color.BLACK);
            lblStatus.setEnabled(false);
            return;
        }
        List<PositionedIssueString> issues = data.issues;
        if (data.nonJavaProof) {
            lblStatus.setText("No Java");
            lblStatus.setIcon((Icon) null);
            lblStatus.setForeground(Color.BLACK);
            lblStatus.setEnabled(false);
            return;
        }

        lblStatus.setText("Javac (" + issues.size() + ")");
        lblStatus.setEnabled(true);

        if (issues.isEmpty()) {
            lblStatus.setIcon(ICON_CHECK.get(16));
            lblStatus.setForeground(COLOR_FINE.get());
        } else {
            boolean onlyWarnings = issues.stream()
                    .allMatch(it -> it.getKind() != PositionedIssueString.Kind.ERROR);
            if (onlyWarnings) {
                lblStatus.setIcon(ICON_WARN.get(16));
                lblStatus.setForeground(COLOR_WARN.get());
            } else {
                lblStatus.setIcon(ICON_ERROR.get(16));
                lblStatus.setForeground(COLOR_ERROR.get());
            }
        }
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return Collections.singletonList(lblStatus);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
        /* ignored */
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        loadProof(e.getSource().getSelectedProof());
    }

    public SettingsProvider getSettings() {
        return new JavacSettingsProvider();
    }
}


/**
 * Stores diagnostics produced when compiling a Java source file.
 *
 * @author Alexander Weigl
 */
@NullMarked
class JavacData {
    /**
     * The diagnostics emitted by the compiler.
     */
    @Nullable
    List<PositionedIssueString> issues = null;
    /**
     * True if there was no Java source file to compile.
     */
    boolean nonJavaProof;
}
