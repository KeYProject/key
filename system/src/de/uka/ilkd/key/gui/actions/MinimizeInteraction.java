package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

public class MinimizeInteraction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 3453843972242689758L;

    public MinimizeInteraction(MainWindow mainWindow) {
	super(mainWindow);
	setTooltip("If ticked and automated strategy (play button) is used, the prover tries to minimize user interaction, "+ 
	"e.g  if the prover can find instantiations by itself, it will not ask the user to provide them. ");
	setName("Minimize Interaction");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
	getMediator().setStupidMode(b);
	ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(b);
//	ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setTacletFilter(b);
    }

}
