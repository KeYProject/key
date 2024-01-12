/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement;

import java.awt.*;
import java.awt.event.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import javax.swing.*;
import javax.swing.event.MouseInputAdapter;

import de.uka.ilkd.key.gui.KeYFileChooser;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A small basic dialog of the ProofManagementExtension which allows the configuration of the check
 * command via the GUI.
 *
 * @author Wolfram Pfeifer
 */
class CheckConfigDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(CheckConfigDialog.class);

    private final JCheckBox missingProofsCheck = new JCheckBox("Missing Proofs Checker");
    private final JCheckBox settingsCheck = new JCheckBox("Settings Checker");
    private final JCheckBox replayCheck = new JCheckBox("Replay Checker");
    private final JCheckBox dependencyCheck = new JCheckBox("Dependency Checker");
    private final JButton runButton = new JButton("Run checkers");
    private final JButton cancelButton = new JButton("Cancel");

    private final JTextField bundleFileField = new JTextField();
    private final JCheckBox reportCheck = new JCheckBox("Generate Report");
    private final JTextField reportFileField = new JTextField();

    private final Component glassPane = new BlockingGlassPane();

    private transient SwingWorker<Void, Void> checkWorker;

    private class ProofManagementCheckWorker extends SwingWorker<Void, Void> {
        @Override
        protected Void doInBackground() throws Exception {
            Path reportPath = null;
            if (reportCheck.isSelected()) {
                reportPath = Paths.get(reportFileField.getText());
                if (Files.isDirectory(reportPath)) {
                    // add default name
                    reportPath = reportPath.resolve("report.html");
                }
            }

            Main.check(missingProofsCheck.isSelected(),
                settingsCheck.isSelected(),
                replayCheck.isSelected(),
                dependencyCheck.isSelected(),
                Paths.get(bundleFileField.getText()),
                reportPath);
            if (reportPath != null) {
                // automatically open the report in browser
                Desktop.getDesktop().open(reportPath.toFile());
            }
            return null;
        }

        @Override
        protected void done() {
            CheckConfigDialog.this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            glassPane.setVisible(false);
            cancelButton.setEnabled(true);
            runButton.setText("Run checkers");
            setCursor(new Cursor(Cursor.DEFAULT_CURSOR));
            if (isCancelled()) {
                LOGGER.info("ProofManagement was cancelled by the user!");
            } else {
                CheckConfigDialog.this.setVisible(false);
            }
        }
    }

    /**
     * Pane that is fully transparent but blocks inputs from user to the underlying component(s).
     * This creates the effect of a "locked" GUI (while the check is running). The "stop" button
     * is not blocked to allow the user to interrupt the running proof management check. This may
     * lead to exceptions though.
     *
     * @author Wolfram Pfeifer
     */
    private class BlockingGlassPane extends JComponent {
        BlockingGlassPane() {
            addMouseListener(new MouseInputAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    // This is not optimal, e.g., it does not update the GUI (i.e. pressed state of
                    // the button). A proper forwarding of the events to the underlying stop button
                    // would be nice, but this is much more difficult to implement correctly.
                    Point glassPanePoint = e.getPoint();
                    Point containerPoint =
                        SwingUtilities.convertPoint(BlockingGlassPane.this,
                            glassPanePoint,
                            getContentPane());
                    Component component =
                        SwingUtilities.getDeepestComponentAt(getContentPane(),
                            containerPoint.x,
                            containerPoint.y);
                    if (component == runButton) {
                        checkWorker.cancel(true);
                    } else {
                        e.consume();
                    }
                }

                @Override
                public void mousePressed(MouseEvent e) {
                    e.consume();
                }

                @Override
                public void mouseReleased(MouseEvent e) {
                    e.consume();
                }

                @Override
                public void mouseEntered(MouseEvent e) {
                    e.consume();
                }

                @Override
                public void mouseExited(MouseEvent e) {
                    e.consume();
                }

                @Override
                public void mouseWheelMoved(MouseWheelEvent e) {
                    e.consume();
                }

                @Override
                public void mouseDragged(MouseEvent e) {
                    e.consume();
                }

                @Override
                public void mouseMoved(MouseEvent e) {
                    e.consume();
                }
            });
            addKeyListener(new KeyListener() {
                @Override
                public void keyPressed(KeyEvent e) {
                    e.consume();
                }

                @Override
                public void keyReleased(KeyEvent e) {
                    e.consume();
                }

                @Override
                public void keyTyped(KeyEvent e) {
                    e.consume();
                }
            });
            setCursor(new Cursor(Cursor.WAIT_CURSOR));
        }
    }

    public CheckConfigDialog(Frame parent, String title, boolean modal) {
        super(parent, title, modal);

        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

        setLayout(new BorderLayout());

        Box checkersBoxInner = Box.createVerticalBox();
        Box checkersBox = Box.createHorizontalBox();
        checkersBox.setBorder(BorderFactory.createTitledBorder("Available Checkers"));

        // default: run all checks and generate html report
        missingProofsCheck.setSelected(true);
        settingsCheck.setSelected(true);
        replayCheck.setSelected(true);
        dependencyCheck.setSelected(true);
        reportCheck.setSelected(true);

        checkersBoxInner.add(missingProofsCheck);
        checkersBoxInner.add(settingsCheck);
        checkersBoxInner.add(replayCheck);
        checkersBoxInner.add(dependencyCheck);
        checkersBoxInner.add(Box.createVerticalGlue());

        checkersBox.add(checkersBoxInner);
        checkersBox.add(Box.createHorizontalGlue());

        Box centerBox = Box.createVerticalBox();
        centerBox.add(checkersBox);

        Dimension buttonDim = new Dimension(180, 27);
        Box bundleBox = Box.createHorizontalBox();
        bundleBox.setBorder(BorderFactory.createTitledBorder("Proof bundle to check"));
        bundleFileField.setMaximumSize(new Dimension(Integer.MAX_VALUE, buttonDim.height));
        bundleFileField.setEditable(false);
        bundleBox.add(bundleFileField);
        bundleBox.add(Box.createHorizontalStrut(5));
        runButton.setEnabled(false);
        JButton chooseBundleButton = new JButton("Choose file...");
        chooseBundleButton.addActionListener(e -> {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Choose file");
            fc.setFileFilter(KeYFileChooser.PROOF_BUNDLE_FILTER);
            if (fc.showOpenDialog(CheckConfigDialog.this) == JFileChooser.APPROVE_OPTION) {
                bundleFileField.setText(fc.getSelectedFile().toString());
                runButton.setEnabled(true);
            }
        });
        chooseBundleButton.setPreferredSize(buttonDim);
        chooseBundleButton.setMinimumSize(buttonDim);
        bundleBox.add(chooseBundleButton);
        centerBox.add(bundleBox);

        Box reportBox = Box.createVerticalBox();
        reportBox.setBorder(BorderFactory.createTitledBorder("HTML report"));

        Box innerReportBox = Box.createHorizontalBox();
        reportFileField.setMaximumSize(new Dimension(Integer.MAX_VALUE, buttonDim.height));
        reportFileField.setEditable(false);
        innerReportBox.add(reportFileField);
        innerReportBox.add(Box.createHorizontalStrut(5));
        JButton chooseReportLocationButton = new JButton("Choose report location...");
        chooseReportLocationButton
                .setToolTipText("Choose the location or file for the HTML report. " +
                    "By default, the filename will be \"report.html\".");
        reportCheck.addItemListener(e -> {
            if (e.getStateChange() == ItemEvent.SELECTED) {
                chooseReportLocationButton.setEnabled(true);
                reportFileField.setEnabled(true);
            } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                chooseReportLocationButton.setEnabled(false);
                reportFileField.setEnabled(false);
            }
        });

        chooseReportLocationButton.addActionListener(e -> {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Choose file or directory");
            fc.setFileFilter(KeYFileChooser.PROOF_MANAGEMENT_REPORT_FILTER);
            fc.setFileSelectionMode(JFileChooser.FILES_AND_DIRECTORIES);
            if (fc.showOpenDialog(CheckConfigDialog.this) == JFileChooser.APPROVE_OPTION) {
                reportFileField.setText(fc.getSelectedFile().toString());
            }
        });
        chooseReportLocationButton.setPreferredSize(buttonDim);
        chooseReportLocationButton.setMinimumSize(buttonDim);
        innerReportBox.add(chooseReportLocationButton);
        Box reportCheckBoxAlignmentBox = Box.createHorizontalBox();
        reportCheckBoxAlignmentBox.add(reportCheck);
        reportCheckBoxAlignmentBox.add(Box.createHorizontalGlue());
        reportBox.add(reportCheckBoxAlignmentBox);
        reportBox.add(innerReportBox);
        centerBox.add(reportBox);

        runButton.addActionListener(e -> {
            if (bundleFileField.getText().isEmpty()) {
                JOptionPane.showMessageDialog(this, "Please choose a proof bundle to check!",
                    "Error", JOptionPane.ERROR_MESSAGE);
                return;
            }
            setGlassPane(glassPane);
            glassPane.setVisible(true);
            runButton.setText("Stop");
            cancelButton.setEnabled(false);
            CheckConfigDialog.this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
            checkWorker = new ProofManagementCheckWorker();
            checkWorker.execute();
        });
        cancelButton.addActionListener(e -> setVisible(false));

        Box buttonsBox = new Box(BoxLayout.X_AXIS);
        buttonsBox.add(Box.createHorizontalGlue());
        buttonsBox.add(runButton);
        buttonsBox.add(Box.createHorizontalStrut(10));
        buttonsBox.add(cancelButton);
        add(centerBox);
        add(buttonsBox, BorderLayout.SOUTH);
        buttonsBox.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));

        setMinimumSize(new Dimension(400, 320));
        setPreferredSize(new Dimension(600, 400));

        runButton.setEnabled(true);

        pack();
        setLocationRelativeTo(parent);
    }
}
