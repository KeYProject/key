package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.rule.OneStepSimplifier;

public class OneStepSimplificationToggleAction extends MainWindowAction {

    public OneStepSimplificationToggleAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("One Step Simplification");
	
	final boolean oneStepSimplificationOn = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().oneStepSimplification();
	setSelected(oneStepSimplificationOn);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
	ProofSettings.DEFAULT_SETTINGS.getGeneralSettings()
	        .setOneStepSimplification(b);
	OneStepSimplifier.INSTANCE.refresh(getMediator().getSelectedProof());
    }

}
