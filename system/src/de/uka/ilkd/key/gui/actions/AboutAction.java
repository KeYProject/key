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
