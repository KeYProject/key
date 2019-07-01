// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.io.IOException;
import java.net.JarURLConnection;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;
import java.util.zip.ZipFile;

import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;

public class OpenFileAction extends MainWindowAction {

    private final class ProofSelectionDialog extends JDialog {
        private String proofToLoad;

        private ProofSelectionDialog(Path bundlePath) throws IOException {
            super(mainWindow, "", true);

            // read zip
            ZipFile bundle = new ZipFile(bundlePath.toFile());

            // create a list of all *.proof files (only top level in bundle)
            List proofs = bundle.stream()
                                .filter(e -> !e.isDirectory())
                                .filter(e -> e.getName().endsWith(".proof"))  // *.key not allowed!
                                .map(e -> e.getName())
                                .collect(Collectors.toList());

            // show list in a JList
            DefaultListModel<String> model = new DefaultListModel<>();
            model.addAll(proofs);
            JList<String> list = new JList<>(model);
            list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            list.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent mouseEvent) {
                    if (mouseEvent.getClickCount() >= 2) {
                        proofToLoad = list.getSelectedValue();
                        setVisible(false);
                        dispose();
                    }
                }
            });

            //create type scroll pane
            JScrollPane scrollPane = new JScrollPane(list);
            scrollPane.setBorder(new TitledBorder("Proofs found in bundle:"));
            Dimension scrollPaneDim = new Dimension(500, 600);
            scrollPane.setPreferredSize(scrollPaneDim);
            scrollPane.setMinimumSize(scrollPaneDim);
            getContentPane().add(scrollPane);

            //create button panel
            JPanel buttonPanel = new JPanel();
            buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
            Dimension buttonDim = new Dimension(100, 27);
            getContentPane().add(buttonPanel);

            //create "ok" button
            JButton okButton = new JButton("OK");
            okButton.setPreferredSize(buttonDim);
            okButton.setMinimumSize(buttonDim);
            okButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    proofToLoad = list.getSelectedValue();
                    setVisible(false);
                    dispose();
                }
            });
            buttonPanel.add(okButton);
            getRootPane().setDefaultButton(okButton);

            //create "cancel" button
            JButton cancelButton = new JButton("Cancel");
            cancelButton.setPreferredSize(buttonDim);
            cancelButton.setMinimumSize(buttonDim);
            cancelButton.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    setVisible(false);
                    dispose();
                }
            });
            buttonPanel.add(cancelButton);

            //show
            getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
            pack();
            setLocation(70, 70);
            setVisible(true);
        }

        private String getProofName() {
            return proofToLoad;
        }
    }
    
    /**
     * 
     */
    private static final long serialVersionUID = -8548805965130100236L;

    public OpenFileAction(MainWindow mainWindow) {
	super(mainWindow);
        setName("Load");
        setIcon(IconFactory.openKeYFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Browse and load problem or proof files.");
        setAcceleratorLetter(KeyEvent.VK_O);
    }

    public void actionPerformed(ActionEvent e) {
        KeYFileChooser keYFileChooser = 
            KeYFileChooser.getFileChooser("Select file to load proof or problem");

        boolean loaded = keYFileChooser.showOpenDialog(mainWindow);

        if (loaded) {
            File file = keYFileChooser.getSelectedFile();
            if (file.toString().endsWith(".zproof")) {
                try {
                    String proofName = new ProofSelectionDialog(file.toPath()).getProofName();
                    if (proofName != null) {
                        mainWindow.loadProblem(file, proofName);
                    }
                    return;
                } catch (IOException exc) {
                    ExceptionDialog.showDialog(mainWindow, exc);
                }
            }
            if (ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getNotifyLoadBehaviour() &&
                    file.toString().endsWith(".java")) {
                JCheckBox checkbox = new JCheckBox("Don't show this warning again");
                Object[] message = { "When you load a Java file, all java files in the current",
                        "directory and all subdirectories will be loaded as well.",
                        checkbox };
                JOptionPane.showMessageDialog(mainWindow, message,
                        "Please note", JOptionPane.WARNING_MESSAGE);
                ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                            .setNotifyLoadBehaviour(!checkbox.isSelected());
                ProofIndependentSettings.DEFAULT_INSTANCE.saveSettings();
            }
            mainWindow.loadProblem(file);
        }

    }
}