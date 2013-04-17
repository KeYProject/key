// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JDialog;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;

public class AboutAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 8240213594748334802L;

    public AboutAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("About KeY");
	// About KeY
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showAbout();
    }

    public void showAbout() {
	String aspects = mainWindow.compiledAspects();
	JOptionPane pane = new JOptionPane(Main.COPYRIGHT
	        + "\n\nWWW: http://key-project.org\n\nVersion "
	        + Main.VERSION
	        + ((aspects.length() == 0) ? "" : "\nCompiled with Aspects:\n"
	                + aspects), JOptionPane.INFORMATION_MESSAGE,
	        JOptionPane.DEFAULT_OPTION, IconFactory.keyLogo(105, 60));
	JDialog dialog = pane.createDialog(mainWindow, "The KeY Project");
	dialog.setVisible(true);
    }

}