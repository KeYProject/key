/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.CardLayout;
import java.awt.Color;
import java.awt.Container;
import java.awt.Dimension;
import java.io.File;
import java.util.LinkedList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.settings.ProofIndependentSettings;


/**
 * @author Benjamin Niedermann
 * @author M. Ulbrich (revisions)
 * @author Wolfram Pfeifer (renamed, reformatting/cleanup, smaller bugfixes)
 */
public class LoadUserTacletsDialog extends JPanel {
    private static final long serialVersionUID = 1L;

    /** the text to be displayed when the "Help" button is pressed */
    private static final String HELP_TEXT =
        "In this dialog you can choose the files that are used for loading user-defined taclets:"
            + "\n\n"
            + "User-Defined Taclets:\nThis file contains the taclets that should be loaded, so that "
            + "they can be used for the current proof. For each taclet an extra proof obligation is "
            + "built that must be provable, in order to sustain the correctness of the calculus.\n\n"
            + "Definitions:\n"
            + "This file contains the signature (function symbols, predicate symbols, sorts)"
            + " that are used for creating the proof obligations mentioned above. In most cases it "
            + "should be the same file as indicated in 'User-Defined Taclets'.\n\n"
            + "Axioms:\nIn order to prove the correctness of the created lemmata,"
            + " for some user-defined taclets the introduction "
            + "of additional axioms is necessary. At this point you can add them.\n"
            + "Beware of the fact that it is crucial for the correctness of the calculus that the used "
            + "axioms are consistent."
            + "It is the responsibility of the user to guarantee this consistency.\n\n"
            + "Technical Remarks:\nThe axioms must be stored in another file than the user-defined "
            + "taclets. Furthermore the axioms are only loaded for the lemmata, but not for the "
            + "current proof.";

    /** warning text that will be shown when loading taclets without proving them */
    private static final String INFO_TEXT =
        "Be aware of the fact that you are going to load taclets\n"
            + "without creating corresponding proof obligations!\n"
            + "In case that the taclets that you want to load are unsound,\n"
            + "the calculus will become unsound!";

    /** this dialog can be in one of two modes (started from different actions) */
    public enum Mode {
        /** only prove taclets but do not add them to current proof */
        PROVE,

        /** load taclets into current proof environment but allow also their proof */
        LOAD
    }

    private class UserTacletFileBox extends Box {
        private static final long serialVersionUID = 1L;
        private File chosenFile;
        private JButton chooseFileButton;
        private JTextField fileField;
        private final String title;

        public UserTacletFileBox(String title) {

            super(BoxLayout.Y_AXIS);
            this.title = title;
            Box box = Box.createHorizontalBox();

            if (title != null) {
                this.setBorder(BorderFactory.createTitledBorder(title));
            }

            box.add(getFileField());
            box.add(Box.createHorizontalStrut(5));
            box.add(getChooseFileButton());
            this.add(box);
        }

        private JTextField getFileField() {
            if (fileField == null) {
                fileField = new JTextField();
                setMaximumHeight(fileField, getChooseFileButton().getPreferredSize().height);
                setMaximumWidth(fileField, Integer.MAX_VALUE);
                fileField.setEditable(false);
            }
            return fileField;
        }

        private JButton getChooseFileButton() {
            if (chooseFileButton == null) {
                chooseFileButton = new JButton("Choose...");
                setMaximumWidth(chooseFileButton,
                    getRemoveAxiomFileButton().getPreferredSize().width);
                chooseFileButton.addActionListener(e -> {
                    File file = chooseFiles(title);
                    if (file != null) {
                        fileHasBeenChosen();
                        setChosenFile(file);
                    }
                });
            }
            return chooseFileButton;
        }

        protected void fileHasBeenChosen() {
            if (okButton != null) {
                okButton.setEnabled(true);
            }
        }

        public void setChosenFile(File file) {
            chosenFile = file;
            getFileField().setText(chosenFile.toString());
        }

        public File getChosenFile() {
            return chosenFile;
        }
    }

    private static final Dimension MAX_DIM = new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);

    private JList<File> axiomsList;
    private JButton addAxiomFileButton;
    private JButton removeAxiomFileButton;
    private JButton helpButton;
    private UserTacletFileBox userTacletFileBox;
    private JPanel axiomFilePanel;
    private JPanel buttonPanel;
    private JScrollPane scrollPane;
    private JDialog helpWindow;

    private JButton okButton;
    private JButton cancelButton;

    private JCheckBox lemmaCheckbox;

    private boolean closedByOkButton = false;
    private final DefaultListModel<File> listModel = new DefaultListModel<>();
    private boolean firstTimeAddingAxioms = true;
    private final Mode mode;
    private JDialog dialog;
    private JPanel justificationPanel;
    private JPanel cardPanel;

    /**
     * Creates a new dialog for loading user-defined taclets
     *
     * @param mode either {@link Mode#PROVE} or {@link Mode#LOAD}
     */
    public LoadUserTacletsDialog(Mode mode) {

        this.mode = mode;

        this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

        this.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));

        this.add(Box.createVerticalStrut(15));
        this.add(getUserTacletFileBox());
        this.add(Box.createVerticalStrut(10));
        if (mode == Mode.LOAD) {
            // with a checkbox and the background to choose.
            this.add(getJustificationBox());
        } else if (mode == Mode.PROVE) {
            this.add(getAxiomFilePanel());
        }
        this.add(Box.createVerticalGlue());
        this.add(Box.createVerticalStrut(5));
    }

    public List<File> getFilesForAxioms() {
        List<File> files = new LinkedList<>();
        Object[] objects = listModel.toArray();
        if (objects != null) {
            for (Object file : objects) {
                files.add((File) file);
            }
        }
        return files;
    }

    public File getFileForTaclets() {
        return userTacletFileBox.getChosenFile();
    }

    private JCheckBox getLemmaCheckBox() {
        if (lemmaCheckbox == null) {
            lemmaCheckbox = new JCheckBox("Generate proof obligations for taclets");
            lemmaCheckbox.setSelected(true);
            lemmaCheckbox.addActionListener(e -> {

                InfoDialog infoDialog = new InfoDialog();
                if (!lemmaCheckbox.isSelected()) {
                    lemmaCheckbox.setSelected(true);
                    boolean showDialogUsingAxioms = ProofIndependentSettings.DEFAULT_INSTANCE
                            .getLemmaGeneratorSettings().isShowingDialogUsingAxioms();
                    if (!showDialogUsingAxioms
                            || infoDialog.showDialog(INFO_TEXT, LoadUserTacletsDialog.this)) {
                        changedToNotSelected();
                        lemmaCheckbox.setSelected(false);
                        ProofIndependentSettings.DEFAULT_INSTANCE.getLemmaGeneratorSettings()
                                .setShowDialogUsingAxioms(
                                    showDialogUsingAxioms && infoDialog.showThisDialogNextTime());
                    }
                } else {
                    changedToSelected();
                }
            });
        }
        return lemmaCheckbox;
    }

    private void enableAxiomFilePanel(boolean val) {
        getAddAxiomFileButton().setEnabled(val);
        getRemoveAxiomFileButton().setEnabled(val);
        getAxiomsList().setEnabled(val);

        CardLayout cl = (CardLayout) getCardPanel().getLayout();
        cl.show(getCardPanel(), Boolean.toString(val));
    }

    private void changedToSelected() {
        enableAxiomFilePanel(true);
    }

    private void changedToNotSelected() {
        enableAxiomFilePanel(false);
    }

    private JList<File> getAxiomsList() {
        if (axiomsList == null) {
            axiomsList = new JList<>();
            axiomsList.setModel(listModel);
            axiomsList.setBorder(BorderFactory.createEtchedBorder());
        }
        return axiomsList;
    }

    private JButton getHelpButton() {
        if (helpButton == null) {
            helpButton = new JButton("Help");
            helpButton.setPreferredSize(getCancelButton().getPreferredSize());
            helpButton.addActionListener(e -> getHelpWindow().setVisible(true));
        }
        return helpButton;
    }

    private JDialog getHelpWindow() {
        if (helpWindow == null) {
            helpWindow = dialog != null ? new JDialog(dialog) : new JDialog();

            JTextArea textArea = new JTextArea(HELP_TEXT);
            textArea.setWrapStyleWord(true);
            textArea.setLineWrap(true);
            textArea.setEditable(false);
            helpWindow.getContentPane().add(new JScrollPane(textArea));
            helpWindow.setMinimumSize(new Dimension(400, 200));
            helpWindow.setTitle("Help");
            helpWindow.pack();
            helpWindow.setLocationRelativeTo(MainWindow.getInstance());

        }
        return helpWindow;
    }

    private JScrollPane getScrollPane() {
        if (scrollPane == null) {
            scrollPane =
                new JScrollPane(getAxiomsList(), ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
                    ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);

            scrollPane.setMaximumSize(MAX_DIM);
        }
        return scrollPane;
    }

    private File chooseFiles(String title) {
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(title);
        fileChooser.setFileFilter(KeYFileChooser.KEY_FILTER);
        if (fileChooser.showOpenDialog(this) == JFileChooser.APPROVE_OPTION) {
            // user pressed OK button
            return fileChooser.getSelectedFile();
        } else {
            // user pressed Cancel button
            return null;
        }
    }

    private UserTacletFileBox getUserTacletFileBox() {
        if (userTacletFileBox == null) {
            userTacletFileBox = new UserTacletFileBox("File with user-defined taclets");
        }
        return userTacletFileBox;
    }

    private JButton getAddAxiomFileButton() {
        if (addAxiomFileButton == null) {
            addAxiomFileButton = new JButton("Add...");

            setMaximumWidth(addAxiomFileButton,
                getRemoveAxiomFileButton().getPreferredSize().width);
            addAxiomFileButton.addActionListener(e -> {

                if (firstTimeAddingAxioms && ProofIndependentSettings.DEFAULT_INSTANCE
                        .getLemmaGeneratorSettings().isShowingDialogAddingAxioms()) {

                    InfoDialog infoDialog = new InfoDialog();
                    firstTimeAddingAxioms =
                        !infoDialog.showDialog(INFO_TEXT, LoadUserTacletsDialog.this);
                    ProofIndependentSettings.DEFAULT_INSTANCE.getLemmaGeneratorSettings()
                            .setShowDialogAddingAxioms(infoDialog.showThisDialogNextTime());
                    if (firstTimeAddingAxioms) {
                        return;
                    }
                }
                File file = chooseFiles("File containing the axioms.");
                if (file != null) {
                    listModel.addElement(file);

                }
            });
        }
        return addAxiomFileButton;
    }

    private JButton getRemoveAxiomFileButton() {
        if (removeAxiomFileButton == null) {
            removeAxiomFileButton = new JButton("Remove");
            removeAxiomFileButton.addActionListener(e -> {
                List<File> values = getAxiomsList().getSelectedValuesList();
                for (File o : values) {
                    listModel.removeElement(o);
                }
            });
        }
        return removeAxiomFileButton;
    }

    private JPanel getAxiomFilePanel() {
        if (axiomFilePanel == null) {
            axiomFilePanel = new JPanel();
            axiomFilePanel.setLayout(new BoxLayout(axiomFilePanel, BoxLayout.X_AXIS));

            axiomFilePanel.add(getScrollPane());
            axiomFilePanel.add(Box.createHorizontalStrut(5));
            axiomFilePanel.add(getButtonPanel());
            axiomFilePanel.setBorder(
                BorderFactory.createTitledBorder("Files with declarations and axioms"));
        }
        return axiomFilePanel;
    }

    private JPanel getJustificationBox() {
        if (justificationPanel == null) {
            justificationPanel = new JPanel();
            justificationPanel.setLayout(new BoxLayout(justificationPanel, BoxLayout.Y_AXIS));
            justificationPanel.setBorder(BorderFactory.createTitledBorder("Prove taclets"));

            Box box = Box.createHorizontalBox();
            box.add(getLemmaCheckBox());
            box.add(Box.createHorizontalGlue());
            justificationPanel.add(box);
            justificationPanel.add(Box.createVerticalStrut(10));

            justificationPanel.add(getCardPanel());
        }
        return justificationPanel;
    }

    private JPanel getCardPanel() {
        if (cardPanel == null) {
            cardPanel = new JPanel(new CardLayout());
            cardPanel.add(getAxiomFilePanel(), "true");

            JPanel warning = new JPanel();
            warning.setLayout(new BoxLayout(warning, BoxLayout.Y_AXIS));
            warning.add(Box.createVerticalStrut(10));
            warning.add(redLabel("Warning!"));
            warning.add(Box.createVerticalStrut(10));
            warning.add(redLabel("Loading of unproved taclets may jeopardise"));
            warning.add(redLabel("the correctness of your own proofs."));
            cardPanel.add(warning, "false");
        }
        return cardPanel;
    }

    private JLabel redLabel(String label) {
        JLabel w = new JLabel(label);
        w.setForeground(Color.red);
        return w;
    }

    private JPanel getButtonPanel() {
        if (buttonPanel == null) {
            buttonPanel = new JPanel();
            buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.Y_AXIS));
            buttonPanel.add(Box.createVerticalGlue());
            buttonPanel.add(getAddAxiomFileButton());
            buttonPanel.add(Box.createVerticalStrut(5));
            buttonPanel.add(getRemoveAxiomFileButton());
            buttonPanel.add(Box.createVerticalGlue());
        }
        return buttonPanel;
    }

    private void setMaximumHeight(JComponent comp, int value) {
        Dimension dim = comp.getMaximumSize();
        dim.height = value;
        comp.setMaximumSize(dim);
    }

    private void setMaximumWidth(JComponent comp, int value) {
        Dimension dim = comp.getMaximumSize();
        dim.width = value;
        comp.setMaximumSize(dim);
    }

    private JDialog getDialog() {
        if (dialog == null) {
            dialog = new JDialog(MainWindow.getInstance());
            if (mode == Mode.LOAD) {
                dialog.setTitle("Load user-defined taclets into proof");
            } else if (mode == Mode.PROVE) {
                dialog.setTitle("Prove user-defined taclets");
            }
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            Container pane = dialog.getContentPane();

            pane.setLayout(new BoxLayout(pane, BoxLayout.Y_AXIS));

            pane.add(this);
            pane.add(Box.createVerticalStrut(5));
            JPanel buttonPane = new JPanel();
            buttonPane.setLayout(new BoxLayout(buttonPane, BoxLayout.X_AXIS));
            buttonPane.add(getHelpButton());
            buttonPane.add(Box.createHorizontalGlue());
            buttonPane.add(getOkButton());
            buttonPane.add(Box.createHorizontalStrut(10));
            buttonPane.add(getCancelButton());
            buttonPane.add(Box.createHorizontalStrut(5));
            buttonPane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
            pane.add(buttonPane);
            dialog.pack();
            dialog.setLocationRelativeTo(MainWindow.getInstance());
        }
        return dialog;
    }

    private JButton getOkButton() {
        if (okButton == null) {
            okButton = new JButton("OK");
            Dimension dim = getCancelButton().getPreferredSize();
            okButton.setEnabled(false);
            okButton.setPreferredSize(dim);
            okButton.addActionListener(e -> {
                getDialog().dispose();
                closedByOkButton = true;
            });
        }
        return okButton;
    }

    private JButton getCancelButton() {
        if (cancelButton == null) {
            cancelButton = new JButton("Cancel");
            cancelButton.addActionListener(e -> {
                getDialog().dispose();
                closedByOkButton = false;
            });
            GuiUtilities.attachClickOnEscListener(cancelButton);
        }
        return cancelButton;
    }

    public boolean showAsDialog() {

        getDialog().setModal(true);
        getDialog().setVisible(true);
        return closedByOkButton;
    }

    public boolean isGenerateProofObligations() {
        return this.getLemmaCheckBox().isSelected();
    }
}
