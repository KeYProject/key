/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;

import java.awt.*;
import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import javax.annotation.Nonnull;
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
import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extensions provides Javac checks for recent-loaded Java files.
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
public class JavacExtension
        implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup,
        KeYSelectionListener {
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

    private KeYMediator mediator;

    /**
     * Initialize the extension. Adds interactivity to the {@link #lblStatus}.
     */
    public JavacExtension() {
        lblStatus.addActionListener(ev -> {
            if (mediator != null && mediator.getSelectedProof() != null) {
                try {
                    JavacData data = mediator.getSelectedProof().getUserData().get(JavacData.class);
                    if (data.nonJavaProof) {
                        JOptionPane.showMessageDialog(MainWindow.getInstance(),
                            "The current proof contains no Java model.");
                        return;
                    }
                    if (data.issues.isEmpty()) {
                        JOptionPane.showMessageDialog(MainWindow.getInstance(),
                            "No Javac issues found.");
                        return;
                    }
                    IssueDialog is =
                        new IssueDialog(MainWindow.getInstance(), "Java Compiler Diagnostics",
                            "The Java compiler issued these diagnostics for your source code:",
                            new TreeSet<>(data.issues));
                    is.setVisible(true);
                } catch (IllegalStateException e) {
                    LOGGER.info("No Javac information available for current proof.");
                }
            }
        });
    }

    private void loadProof(Proof selectedProof) throws RuntimeException {
        try {
            if (selectedProof != null) {
                JavacData data = selectedProof.getUserData().get(JavacData.class);
                updateLabel(data);
            } else {
                updateLabel(null);
            }
        } catch (IllegalStateException e) {
            JavacData data = new JavacData();
            selectedProof.getUserData().register(data);
            final JavaModel jm = selectedProof.getServices().getJavaModel();

            if (jm == JavaModel.NO_MODEL) {
                data.nonJavaProof = true;
                updateLabel(data);
                return;
            }

            File bootClassPath =
                jm.getBootClassPath() != null ? new File(jm.getBootClassPath()) : null;
            List<File> classpath = jm.getClassPathEntries();
            File javaPath = new File(jm.getModelDir());

            lblStatus.setForeground(Color.black);
            lblStatus.setText("Javac runs");
            lblStatus.setIcon(ICON_WAIT.get(16));

            CompletableFuture<List<PositionedIssueString>> task =
                JavaCompilerCheckFacade.check(mediator.getUI(), bootClassPath, classpath, javaPath);
            try {
                task.thenAccept(it -> SwingUtilities.invokeLater(() -> {
                    lblStatus.setText("Javac finished");
                    data.issues.addAll(it);
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
     * @param data data to use
     */
    private void updateLabel(JavacData data) {
        if (data == null || data.issues == null) {
            lblStatus.setText("Javac");
            lblStatus.setIcon(null);
            lblStatus.setForeground(Color.BLACK);
            lblStatus.setEnabled(false);
            return;
        }
        if (data.nonJavaProof) {
            lblStatus.setText("No Java");
            lblStatus.setIcon(null);
            lblStatus.setForeground(Color.BLACK);
            lblStatus.setEnabled(false);
            return;
        }

        lblStatus.setText("Javac (" + data.issues.size() + ")");
        lblStatus.setEnabled(true);

        if (data.issues.isEmpty()) {
            lblStatus.setIcon(ICON_CHECK.get(16));
            lblStatus.setForeground(COLOR_FINE.get());
        } else {
            boolean onlyWarnings = data.issues.stream()
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
    public void selectedNodeChanged(KeYSelectionEvent e) {
        /* ignored */
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        loadProof(e.getSource().getSelectedProof());
    }
}


/**
 * Stores diagnostics produced when compiling a Java source file.
 *
 * @author Alexander Weigl
 */
class JavacData {
    /**
     * The diagnostics emitted by the compiler.
     */
    @Nonnull
    final List<PositionedIssueString> issues = new ArrayList<>(0);
    /**
     * True if there was no Java source file to compile.
     */
    boolean nonJavaProof;
}
