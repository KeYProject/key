package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;

public class PrettyPrintToggleAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 8633254204256247698L;

    public PrettyPrintToggleAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Use pretty syntax");
	setAcceleratorLetter(KeyEvent.VK_P);
	setTooltip("If ticked, infix notations are used.");
	setSelected(NotationInfo.PRETTY_SYNTAX);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	NotationInfo.PRETTY_SYNTAX = ((JCheckBoxMenuItem) e.getSource())
	        .isSelected();
	mainWindow.makePrettyView();
    }

}
