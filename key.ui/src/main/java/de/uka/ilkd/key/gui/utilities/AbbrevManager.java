/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.IOException;
import java.lang.ref.WeakReference;
import java.nio.file.Files;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This is a small extension that add the abbreviation widget to KeY.
 * The abbreviation manager allows you to manage (delete, rename, load/save,...)
 * abbreviations in KeY proofs.
 *
 * @author Alexander Weigl
 * @version 1 (14.07.23)
 */
@KeYGuiExtension.Info(name = "Abbreviation Manager",
    description = "A widget for the management of abbreviation in proofs. " +
        "Allows storing and loading abbreviations of text files.",
    disabled = false,
    experimental = false)
@NullMarked
public class AbbrevManager implements KeYGuiExtension, KeYGuiExtension.LeftPanel {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbbrevManager.class);

    private AbbrevManagerPanel panel;

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        if (panel == null)
            panel = new AbbrevManagerPanel(window, mediator);
        return Collections.singleton(panel);
    }

    private static class AbbrevManagerPanel extends JPanel implements TabPanel {
        /**
         * seperator between abbreviation label and term inside of stored files
         */
        public static final String SEPERATOR_ABBREV_FILE = "::==";

        private final KeYMediator mediator;

        private final JList<Pair<Term, String>> listAbbrev = new JList<>();
        private final DefaultListModel<Pair<Term, String>> modelAbbrev = new DefaultListModel<>();
        private final KeyAction actionLoad = new LoadAction();
        private final KeyAction actionSave = new SaveAction();
        private final KeyAction actionTransfer = new TransferAbbrevAction();

        private final PropertyChangeListener updateListListener = it -> updateList();
        private final MainWindow window;

        /**
         * Stores a reference to the proof to which the {@link #updateListListener} is attached to.
         * Weak ref protects for memory leakage.
         */
        @Nullable
        private WeakReference<Proof> oldProof;

        public AbbrevManagerPanel(MainWindow window, KeYMediator mediator) {
            this.window = window;
            this.mediator = mediator;
            setLayout(new BorderLayout());
            listAbbrev.setModel(modelAbbrev);
            listAbbrev.setCellRenderer(new DefaultListCellRenderer() {
                @Override
                public Component getListCellRendererComponent(JList<?> list, Object value,
                        int index, boolean isSelected, boolean cellHasFocus) {
                    var v = (Pair<Term, String>) value;
                    var s = v.second + " : "
                        + LogicPrinter.quickPrintTerm(v.first, mediator.getServices());
                    return super.getListCellRendererComponent(list, s, index, isSelected,
                        cellHasFocus);
                }
            });
            add(listAbbrev);

            updateList();

            mediator.addKeYSelectionListener(new KeYSelectionListener() {
                @Override
                public void selectedProofChanged(KeYSelectionEvent e) {
                    // if oldProof exists, remove updateListListener from it.
                    if (oldProof != null) {
                        var oldp = oldProof.get();
                        if (oldp != null) {
                            oldp.abbreviations().removePropertyChangeListener(updateListListener);
                        }
                        oldProof = null;
                    }
                    // if currently there is a selected proof, attach updateListListener to it
                    final var selectedProof = mediator.getSelectedProof();
                    if (selectedProof != null) {
                        selectedProof.abbreviations().addPropertyChangeListener(updateListListener);
                        oldProof = new WeakReference<>(selectedProof);
                    }
                    updateList();
                }
            });

            mediator.getNotationInfo().getAbbrevMap().addPropertyChangeListener(updateListListener);

            final var popup = new JPopupMenu();
            popup.add(new RemoveAbbrev());
            popup.add(new ChangeAbbrev());
            popup.add(new ChangeTerm());
            popup.add(new ToggleActivity());
            listAbbrev.setComponentPopupMenu(popup);
        }

        private void updateList() {
            modelAbbrev.clear();
            var selectedProof = mediator.getSelectedProof();
            if (selectedProof != null) {
                selectedProof.abbreviations().export()
                        .stream()
                        .sorted(Comparator.comparing(it -> it.second))
                        .forEach(modelAbbrev::addElement);
            }
        }

        @Override
        public String getTitle() {
            return "Abbrev Manager";
        }

        @Override
        public JComponent getComponent() {
            return this;
        }

        @Override
        public Collection<Action> getTitleActions() {
            return List.of(actionLoad, actionSave, actionTransfer);
        }

        private class SaveAction extends KeyAction {
            public SaveAction() {
                setName("Save abbreviations");
                setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
                setTooltip("Save abbreviation to file.");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                KeYFileChooser fc =
                    KeYFileChooser.getFileChooser("Select file to store abbreviation map.");
                int result = fc.showOpenDialog(window);
                if (result == JFileChooser.APPROVE_OPTION) {
                    var abbrevMap = mediator.getNotationInfo().getAbbrevMap().export();
                    var file = fc.getSelectedFile().toPath();
                    try {
                        Files.writeString(file,
                            abbrevMap.stream().map(it -> it.second + SEPERATOR_ABBREV_FILE +
                                    LogicPrinter.quickPrintTerm(it.first, mediator.getServices()))
                                    .collect(Collectors.joining("\n")));
                    } catch (IOException ex) {
                        LOGGER.error("File I/O error", ex);
                        JOptionPane.showMessageDialog(window, "I/O Error:" + ex.getMessage());
                    }
                }
            }
        }

        private class LoadAction extends KeyAction {
            public LoadAction() {
                setName("Load abbreviations");
                setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
                setTooltip("Load abbreviation from a given file.");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                KeYFileChooser fc =
                    KeYFileChooser.getFileChooser("Select file to load proof or problem");
                var mainWindow = window;
                int result = fc.showOpenDialog(mainWindow);
                if (result == JFileChooser.APPROVE_OPTION) {
                    var abbrevMap = mediator.getNotationInfo().getAbbrevMap();
                    var kio = new KeyIO(mediator.getServices());
                    kio.setAbbrevMap(abbrevMap);
                    File file = fc.getSelectedFile();

                    try {
                        for (String line : Files.readAllLines(file.toPath())) {
                            if (line.isBlank() || line.startsWith("#") || line.startsWith("//")) {
                                String[] split = line.split(SEPERATOR_ABBREV_FILE);
                                if (split.length == 2) {
                                    var abbrevName = split[0];
                                    var term = kio.parseExpression(split[1]);
                                    try {
                                        abbrevMap.put(term, abbrevName.trim(), true);
                                    } catch (AbbrevException ex) {
                                        LOGGER.error("Could not add {} with {} to abbrevMap",
                                            abbrevName, term, ex);
                                    }
                                }
                            }
                        }
                    } catch (IOException ex) {
                        LOGGER.error("File I/O error", ex);
                        JOptionPane.showMessageDialog(mainWindow, "I/O Error:" + ex.getMessage());
                    }
                }
            }
        }


        private class RemoveAbbrev extends KeyAction {
            public RemoveAbbrev() {
                setName("Remove abbreviation");
                listAbbrev.addListSelectionListener(e -> {
                    final var selectedValue = listAbbrev.getSelectedValue();
                    setEnabled(selectedValue != null);
                });
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                var term = listAbbrev.getSelectedValue().first;
                mediator.getNotationInfo().getAbbrevMap().remove(term);
                window.makePrettyView();
            }
        }

        private class ToggleActivity extends KeyAction {
            public ToggleActivity() {
                setName("Toggle abbreviation");

                listAbbrev.addListSelectionListener(e -> {
                    final var selectedValue = listAbbrev.getSelectedValue();
                    if (selectedValue == null) {
                        setEnabled(false);
                        setName("Toggle abbreviation");
                        return;
                    }
                    setEnabled(true);
                    var term = selectedValue.first;
                    if (mediator.getNotationInfo().getAbbrevMap().isEnabled(term)) {
                        setName("Disable abbreviation");
                    } else {
                        setName("Enable abbreviation");
                    }
                });
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                var term = listAbbrev.getSelectedValue().first;
                var value = mediator.getNotationInfo().getAbbrevMap().isEnabled(term);
                mediator.getNotationInfo().getAbbrevMap().setEnabled(term, !value);
                window.makePrettyView();
            }
        }

        private class ChangeAbbrev extends KeyAction {
            public ChangeAbbrev() {
                setName("Change abbreviation");
                listAbbrev.addListSelectionListener(e -> {
                    final var selectedValue = listAbbrev.getSelectedValue();
                    setEnabled(selectedValue != null);
                });
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                var selected = listAbbrev.getSelectedValue();
                var answer =
                    JOptionPane.showInputDialog(window, "Set new label for term: " + selected.first,
                        selected.second);
                if (answer == null)
                    return;
                try {
                    mediator.getNotationInfo().getAbbrevMap().changeAbbrev(selected.first, answer);
                    window.makePrettyView();
                } catch (AbbrevException ex) {
                    throw new RuntimeException(ex);
                }
            }
        }

        private class ChangeTerm extends KeyAction {
            public ChangeTerm() {
                setName("Change term");
                listAbbrev.addListSelectionListener(e -> {
                    final var selectedValue = listAbbrev.getSelectedValue();
                    setEnabled(selectedValue != null);
                });
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                var selected = listAbbrev.getSelectedValue();
                var prettyPrinted =
                    LogicPrinter.quickPrintTerm(selected.first, mediator.getServices());

                while (true) { // abort if the user abort the input dialog, or the expression was
                               // successfully changed.
                    var answer =
                        JOptionPane.showInputDialog(window,
                            "Set a new term for abbreviation " + selected.second + ":",
                            prettyPrinted);
                    if (answer == null)
                        return;
                    var kio = new KeyIO(mediator.getServices());
                    kio.setAbbrevMap(mediator.getNotationInfo().getAbbrevMap());
                    try {
                        var term = kio.parseExpression(answer);
                        mediator.getNotationInfo().getAbbrevMap().changeAbbrev(selected.second,
                            term, true);
                        window.makePrettyView();
                        return;
                    } catch (BuildingException ex) {
                        LOGGER.error("Error during parsing of user entered term {}", answer, ex);
                        JOptionPane.showMessageDialog(window, ex.getMessage(), "Error",
                            JOptionPane.ERROR_MESSAGE);
                        prettyPrinted = answer;
                    } catch (AbbrevException ex) {
                        throw new RuntimeException(ex);
                    }
                }
            }
        }

        private class TransferAbbrevAction extends KeyAction {
            private final IconFontProvider TRANSFER_ICON =
                new IconFontProvider(FontAwesomeSolid.ANGLE_DOUBLE_DOWN,
                    Color.black);

            public TransferAbbrevAction() {
                setName("Transfer abbreviation from...");
                setIcon(TRANSFER_ICON.get());
                setTooltip(
                    "Transfers all abbreviation from the selected proof to this proof. Best effort. No guarantees!");
            }

            @Override
            public void actionPerformed(ActionEvent e) {
                var selected = mediator.getSelectedProof();
                if (selected == null)
                    return;

                var proofs = window.getProofList().getModel().getLoadedProofs()
                        .stream().filter(it -> it != selected)
                        .toArray(Proof[]::new);
                var from = (Proof) JOptionPane.showInputDialog(window,
                    "Select a proof to import from. ", "Import Abbreviations",
                    JOptionPane.PLAIN_MESSAGE, null, proofs, null);
                if (from == null)
                    return;
                var kio = new KeyIO(mediator.getServices());
                kio.setAbbrevMap(selected.abbreviations());

                for (Pair<Term, String> pair : from.abbreviations().export()) {
                    // print and parse to ensure the different namespace
                    var term = kio.parseExpression(
                        LogicPrinter.quickPrintTerm(pair.first, from.getServices()));
                    selected.abbreviations().forcePut(pair.second, term);
                }
                window.makePrettyView();
            }
        }

    }

}
