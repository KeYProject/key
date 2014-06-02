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

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

/**
 * for debugging - opens a window with the settings from current Proof and the
 * default settings
 */
public class ShowActiveSettingsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -3038735283059371442L;

    public ShowActiveSettingsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show All Active Settings...");
        setIcon(IconFactory.properties(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {

	String message;

	message = "Default Settings: \n"
	        + ProofSettings.DEFAULT_SETTINGS.settingsToString()
	        + "\n----------\n";
	message += "Settings[CurrentProof]:\n"
	        + ((getMediator().getSelectedProof() == null) ? "No proof loaded."
	                : getMediator().getSelectedProof().getSettings()
	                        .settingsToString());

	final JTextArea settings = new JTextArea(message, 30, 80);
	settings.setEditable(false);
	settings.setLineWrap(true);

	JScrollPane settingsPane = new JScrollPane(settings);

	JOptionPane.showMessageDialog(mainWindow, settingsPane, "Settings used in the current proof",
	        JOptionPane.INFORMATION_MESSAGE);
    }

}