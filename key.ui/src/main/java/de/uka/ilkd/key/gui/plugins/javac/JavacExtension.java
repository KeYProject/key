package de.uka.ilkd.key.gui.plugins.javac;

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
import de.uka.ilkd.key.proof.Proof;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.util.Collections;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.ExecutionException;

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
        implements KeYGuiExtension, KeYGuiExtension.StatusLine, KeYGuiExtension.Startup {
    private final JButton lblStatus = new JButton("Javac");

    private static final ColorSettings.ColorProperty COLOR_FINE =
        ColorSettings.define("javac.fine", "",
            new Color(80, 120, 200));
    private static final ColorSettings.ColorProperty COLOR_ERROR =
        ColorSettings.define("javac.error", "",
            new Color(200, 20, 80));
    private static final ColorSettings.ColorProperty COLOR_WARN =
        ColorSettings.define("javac.warn", "",
            new Color(200, 120, 80));
    private final Logger LOGGER = LoggerFactory.getLogger(JavacExtension.class);

    public static final IconFontProvider ICON_CHECK =
        new IconFontProvider(MaterialDesignRegular.CHECK_BOX, COLOR_FINE.get());

    public static final IconFontProvider ICON_WARN =
        new IconFontProvider(MaterialDesignRegular.WARNING, COLOR_WARN.get());

    public static final IconFontProvider ICON_ERROR =
        new IconFontProvider(MaterialDesignRegular.ERROR_OUTLINE, COLOR_ERROR.get());

    public static final IconFontProvider ICON_WAIT =
        new IconFontProvider(MaterialDesignRegular.WATCH);


    private KeYMediator mediator;


    public JavacExtension() {
        lblStatus.addActionListener(ev -> {
            if (mediator != null) {
                try {
                    var data = mediator.getSelectedProof().getUserData().get(JavacData.class);
                    if (data.nonJavaProof) {
                        JOptionPane.showMessageDialog(MainWindow.getInstance(),
                            "The current proof contains no Java model.");
                        return;
                    }
                    if (data.issues.size() == 0) {
                        JOptionPane.showMessageDialog(MainWindow.getInstance(),
                            "No Javac issues found.");
                        return;
                    }
                    var is = new IssueDialog(MainWindow.getInstance(), "Javac Issues",
                        new TreeSet<>(data.issues), false);
                    is.setVisible(true);
                } catch (IllegalStateException e) {
                    LOGGER.info("No Javac information available for current proof.");
                }
            }
        });
    }

    private void loadProof(Proof selectedProof) throws RuntimeException {
        try {
            var data = selectedProof.getUserData().get(JavacData.class);
            updateLabel(data);
        } catch (IllegalStateException e) {
            var data = new JavacData();
            selectedProof.getUserData().register(data);
            final var jm = selectedProof.getServices().getJavaModel();

            if (jm == null) {
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

            var task =
                JavaCompilerCheckFacade.check(mediator.getUI(), bootClassPath, classpath, javaPath);
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

    private void updateLabel(JavacData data) {
        if (data == null)
            return;
        if (data.nonJavaProof) {
            lblStatus.setText("No Java");
            lblStatus.setForeground(Color.BLACK);
            lblStatus.setEnabled(false);
            return;
        }

        lblStatus.setText("Javac (" + data.issues.size() + ")");

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
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                loadProof(mediator.getSelectedProof());
            }
        });
    }
}


class JavacData {
    List<PositionedIssueString> issues = null;
    boolean nonJavaProof;
}
