package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
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
	final boolean prettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
	NotationInfo.PRETTY_SYNTAX = prettySyntax;
	setSelected(prettySyntax);
	//setSelected(NotationInfo.PRETTY_SYNTAX);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        System.out.println(selected);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(selected);
	NotationInfo.PRETTY_SYNTAX = selected;
	mainWindow.getUnicodeToggleAction().setEnabled(selected);
	mainWindow.makePrettyView();
    }

}
