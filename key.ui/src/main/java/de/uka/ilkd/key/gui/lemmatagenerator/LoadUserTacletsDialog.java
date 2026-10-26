/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.CardLayout;
import java.awt.Color;
import java.awt.Container;
import java.awt.Dimension;
import java.awt.LayoutManager;
import java.io.File;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.IntStream;
import javax.swing.*;

import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * @author Benjamin Niedermann
 * @author M. Ulbrich (revisions)
 * @author Wolfram Pfeifer (renamed, reformatting/cleanup, smaller bugfixes)
 */
@NullMarked
public class LoadUserTacletsDialog extends JPanel {
    private static final long serialVersionUID = 1L;

    /**
     * the text to be displayed when the "Help" button is pressed
     */
    private static final String HELP_TEXT =
        """
                In this dialog you can choose the files that are used for loading user-defined taclets:

                User-Defined Taclets:
                This file contains the taclets that should be loaded, so that they can be used for the current proof. For each taclet an extra proof obligation is built that must be provable, in order to sustain the correctness of the calculus.

                Definitions:
                This file contains the signature (function symbols, predicate symbols, sorts) that are used for creating the proof obligations mentioned above. In most cases it should be the same file as indicated in 'User-Defined Taclets'.

                Axioms:
                In order to prove the correctness of the created lemmata, for some user-defined taclets the introduction of additional axioms is necessary. At this point you can add them.
                Beware of the fact that it is crucial for the correctness of the calculus that the used axioms are consistent.It is the responsibility of the user to guarantee this consistency.

                Technical Remarks:
                The axioms must be stored in another file than the user-defined taclets. Furthermore the axioms are only loaded for the lemmata, but not for the current proof.""";

    /**
     * warning text that will be shown when loading taclets without proving them
     */
    private static final String INFO_TEXT =
        """
                Be aware of the fact that you are going to load taclets
                without creating corresponding proof obligations!
                In case that the taclets that you want to load are unsound,
                the calculus will become unsound!""";

    /**
     * this dialog can be in one of two modes (started from different actions)
     */
    public enum Mode {
        /**
         * only prove taclets but do not add them to current proof
         */
        PROVE,

        /**
         * load taclets into current proof environment but allow also their proof
         */
        LOAD
    }

    private class UserTacletFileBox extends Box {
        private @Nullable Path chosenFile;
        private @Nullable JButton chooseFileButton;
        private @Nullable JTextField fileField;
        private final @Nullable String title;

        /**
         * The box configures its border and child components via the lazy getters while the
         * receiver is still under initialization (EISOP initialization check); the effects only
         * take place after construction completes, suppressed with a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public UserTacletFileBox(@Nullable String title) {

            super(BoxLayout.Y_AXIS);
            this.title = title;
            Box box = createHorizontalBox();

            if (title != null) {
                this.setBorder(BorderFactory.createTitledBorder(title));
            }

            box.add(getFileField());
            box.add(createHorizontalStrut(5));
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
                    String currentTitle = title;
                    if (currentTitle == null) {
                        // the file box is only ever created with a title
                        throw new NullPointerException("No title for the file chooser.");
                    }
                    Path file = chooseFiles(currentTitle);
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

        public void setChosenFile(Path file) {
            chosenFile = file;
            getFileField().setText(file.toString());
        }

        public @Nullable Path getChosenFile() {
            return chosenFile;
        }
    }

    private static final Dimension MAX_DIM = new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);

    private @Nullable JList<Path> axiomsList;
    private @Nullable JButton addAxiomFileButton;
    private @Nullable JButton removeAxiomFileButton;
    private @Nullable JButton helpButton;
    private @Nullable UserTacletFileBox userTacletFileBox;
    private @Nullable JPanel axiomFilePanel;
    private @Nullable JPanel buttonPanel;
    private @Nullable JScrollPane scrollPane;
    private @Nullable JDialog helpWindow;

    private @Nullable JButton okButton;
    private @Nullable JButton cancelButton;

    private @Nullable JCheckBox lemmaCheckbox;

    private boolean closedByOkButton = false;
    private final DefaultListModel<Path> listModel = new DefaultListModel<>();
    private boolean firstTimeAddingAxioms = true;
    private final Mode mode;
    private @Nullable JDialog dialog;
    private @Nullable JPanel justificationPanel;
    private @Nullable JPanel cardPanel;

    /**
     * Creates a new dialog for loading user-defined taclets
     *
     * @param mode either {@link Mode#PROVE} or {@link Mode#LOAD}
     * <p>
     * The dialog configures its layout, borders and child panels via the lazy getters while the
     * receiver is still under initialization (EISOP initialization check) and passes itself to
     * {@code BoxLayout} as container; the effects only take place after construction completes,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:method.invocation.invalid",
        "nullness:argument.type.incompatible" })
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

    public List<Path> getFilesForAxioms() {
        return IntStream.range(0, listModel.size()).mapToObj(listModel::get).toList();
    }

    public @Nullable Path getFileForTaclets() {
        UserTacletFileBox box = getUserTacletFileBox();
        return box.getChosenFile();
    }

    private JCheckBox getLemmaCheckBox() {
        if (lemmaCheckbox == null) {
            JCheckBox checkbox = new JCheckBox("Generate proof obligations for taclets");
            checkbox.setSelected(true);
            checkbox.addActionListener(e -> {

                InfoDialog infoDialog = new InfoDialog();
                if (!checkbox.isSelected()) {
                    checkbox.setSelected(true);
                    boolean showDialogUsingAxioms = ProofIndependentSettings.DEFAULT_INSTANCE
                            .getLemmaGeneratorSettings().isShowingDialogUsingAxioms();
                    if (!showDialogUsingAxioms
                            || infoDialog.showDialog(INFO_TEXT, LoadUserTacletsDialog.this)) {
                        changedToNotSelected();
                        checkbox.setSelected(false);
                        ProofIndependentSettings.DEFAULT_INSTANCE.getLemmaGeneratorSettings()
                                .setShowDialogUsingAxioms(
                                    showDialogUsingAxioms && infoDialog.showThisDialogNextTime());
                    }
                } else {
                    changedToSelected();
                }
            });
            lemmaCheckbox = checkbox;
        }
        return lemmaCheckbox;
    }

    private void enableAxiomFilePanel(boolean val) {
        getAddAxiomFileButton().setEnabled(val);
        getRemoveAxiomFileButton().setEnabled(val);
        getAxiomsList().setEnabled(val);

        JPanel panel = getCardPanel();
        if (panel == null) {
            // the card panel is always available when the axiom panel is enabled
            throw new NullPointerException("No card panel available.");
        }
        LayoutManager layoutManager = panel.getLayout();
        if (!(layoutManager instanceof CardLayout cl)) {
            // the axiom file area is always laid out with a card layout
            throw new NullPointerException("No card layout available.");
        }
        cl.show(panel, Boolean.toString(val));
    }

    private void changedToSelected() {
        enableAxiomFilePanel(true);
    }

    private void changedToNotSelected() {
        enableAxiomFilePanel(false);
    }

    private JList<Path> getAxiomsList() {
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
            JDialog window = dialog != null ? new JDialog(dialog) : new JDialog();

            JTextArea textArea = new JTextArea(HELP_TEXT);
            textArea.setWrapStyleWord(true);
            textArea.setLineWrap(true);
            textArea.setEditable(false);
            window.getContentPane().add(new JScrollPane(textArea));
            window.setMinimumSize(new Dimension(400, 200));
            window.setTitle("Help");
            window.pack();
            window.setLocationRelativeTo(MainWindow.getInstance());
            helpWindow = window;
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

    private @Nullable Path chooseFiles(String title) {
        KeYFileChooser fileChooser = KeYFileChooser.getFileChooser(title);
        fileChooser.setFileFilter(KeYFileChooser.KEY_FILTER);
        if (fileChooser.showOpenDialog(this) == JFileChooser.APPROVE_OPTION) {
            // user pressed OK button
            File selectedFile = fileChooser.getSelectedFile();
            if (selectedFile == null) {
                // the dialog was approved without selecting a file
                return null;
            }
            return selectedFile.toPath();
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
                Path file = chooseFiles("File containing the axioms.");
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
                List<Path> values = getAxiomsList().getSelectedValuesList();
                for (Path o : values) {
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
            JPanel panel = new JPanel();
            panel.setLayout(new BoxLayout(panel, BoxLayout.Y_AXIS));
            panel.setBorder(BorderFactory.createTitledBorder("Prove taclets"));

            Box box = Box.createHorizontalBox();
            box.add(getLemmaCheckBox());
            box.add(Box.createHorizontalGlue());
            panel.add(box);
            panel.add(Box.createVerticalStrut(10));

            panel.add(getCardPanel());
            justificationPanel = panel;
        }
        return justificationPanel;
    }

    private JPanel getCardPanel() {
        if (cardPanel == null) {
            JPanel panel = new JPanel(new CardLayout());
            panel.add(getAxiomFilePanel(), "true");

            JPanel warning = new JPanel();
            warning.setLayout(new BoxLayout(warning, BoxLayout.Y_AXIS));
            warning.add(Box.createVerticalStrut(10));
            warning.add(redLabel("Warning!"));
            warning.add(Box.createVerticalStrut(10));
            warning.add(redLabel("Loading of unproved taclets may jeopardise"));
            warning.add(redLabel("the correctness of your own proofs."));
            panel.add(warning, "false");
            cardPanel = panel;
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
            JDialog win = new JDialog(MainWindow.getInstance());
            if (mode == Mode.LOAD) {
                win.setTitle("Load user-defined taclets into proof");
            } else if (mode == Mode.PROVE) {
                win.setTitle("Prove user-defined taclets");
            }
            win.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            Container pane = win.getContentPane();

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
            win.pack();
            win.setLocationRelativeTo(MainWindow.getInstance());
            dialog = win;
        }
        return dialog;
    }

    private JButton getOkButton() {
        if (okButton == null) {
            JButton button = new JButton("OK");
            Dimension dim = getCancelButton().getPreferredSize();
            button.setEnabled(false);
            button.setPreferredSize(dim);
            button.addActionListener(e -> {
                getDialog().dispose();
                closedByOkButton = true;
            });
            okButton = button;
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
