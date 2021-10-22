package org.key_project.proofmanagement;

import de.uka.ilkd.key.gui.KeYFileChooser;

import javax.swing.*;
import javax.swing.event.MouseInputAdapter;
import java.awt.*;
import java.awt.event.*;
import java.nio.file.Path;
import java.nio.file.Paths;

class CheckConfigDialog extends JDialog {

    private final JCheckBox missingProofsCheck = new JCheckBox("Missing Proofs Checker");
    private final JCheckBox settingsCheck = new JCheckBox("Settings Checker");
    private final JCheckBox replayCheck = new JCheckBox("Replay Checker");
    private final JCheckBox dependencyCheck = new JCheckBox("Dependency Checker");
    private final JButton runButton = new JButton("Run checkers");
    private final JButton cancelButton = new JButton("Cancel");

    private final JTextField bundleFileField = new JTextField();
    private final JTextField reportFileField = new JTextField();

    private final Component glassPane = new BlockingGlassPane();

    SwingWorker<Void, Void> w;

    private class MyWorker extends SwingWorker<Void, Void> {
        @Override
        protected Void doInBackground() throws Exception {
            Path reportPath = reportFileField.getText().isEmpty() ? null :
                Paths.get(reportFileField.getText(), "report.html");
            Main.check(missingProofsCheck.isSelected(),
                settingsCheck.isSelected(),
                replayCheck.isSelected(),
                dependencyCheck.isSelected(),
                Paths.get(bundleFileField.getText()),
                reportPath);
            if (reportPath != null) {
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
                System.out.println("ProofManagement was cancelled by the user!");
            } else {
                CheckConfigDialog.this.setVisible(false);
            }
        }
    }

    private class BlockingGlassPane extends JComponent {
        BlockingGlassPane() {
            this.addMouseListener(new MouseInputAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    // TODO: this is not sufficient, it does not update the GUI (i.e. pressed state
                    //       of the button)
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
                        w.cancel(true);
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

        // default: run all checks
        missingProofsCheck.setSelected(true);
        settingsCheck.setSelected(true);
        replayCheck.setSelected(true);
        dependencyCheck.setSelected(true);

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

        Box reportBox = Box.createHorizontalBox();
        reportBox.setBorder(BorderFactory.createTitledBorder("Report location"));
        reportFileField.setMaximumSize(new Dimension(Integer.MAX_VALUE, buttonDim.height));
        reportFileField.setEditable(false);
        reportBox.add(reportFileField);
        reportBox.add(Box.createHorizontalStrut(5));
        JButton chooseReportLocationButton = new JButton("Choose report location...");

        chooseReportLocationButton.addActionListener(e -> {
            KeYFileChooser fc = KeYFileChooser.getFileChooser("Choose file");
            fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            if (fc.showOpenDialog(CheckConfigDialog.this) == JFileChooser.APPROVE_OPTION) {
                reportFileField.setText(fc.getSelectedFile().toString());
            }
        });
        chooseReportLocationButton.setPreferredSize(buttonDim);
        chooseReportLocationButton.setMinimumSize(buttonDim);
        reportBox.add(chooseReportLocationButton);
        centerBox.add(reportBox);

        runButton.addActionListener(e -> {
            setGlassPane(glassPane);
            glassPane.setVisible(true);
            runButton.setText("Stop");
            cancelButton.setEnabled(false);
            CheckConfigDialog.this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
            w = new MyWorker();
            w.execute();
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

        setMinimumSize(new Dimension(400, 200));
        setPreferredSize(new Dimension(600, 400));

        // for debugging:
        bundleFileField.setText("/home/wolfram/Desktop/prooftest/testbundle.zproof");
        reportFileField.setText("/home/wolfram/Desktop");
        runButton.setEnabled(true);

        pack();
        setLocationRelativeTo(parent);
    }
}
