package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ViewSelector;

public class ToolTipOptionsAction extends MainWindowAction {

    public ToolTipOptionsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("ToolTip options");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	 ViewSelector vselector = new ViewSelector(mainWindow);
	 vselector.setVisible(true);
    }

}
