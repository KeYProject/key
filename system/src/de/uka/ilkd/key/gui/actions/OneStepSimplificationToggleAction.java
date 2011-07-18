package de.uka.ilkd.key.gui.actions;

import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.AbstractButton;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.rule.OneStepSimplifier;

public class OneStepSimplificationToggleAction extends MainWindowAction {

    public OneStepSimplificationToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("One Step Simplification");
        putValue(MNEMONIC_KEY, KeyEvent.VK_O);
        putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke("control shift S"));
        putValue(SHORT_DESCRIPTION, "Toggle the aggregation of simplification rules." +
        		" Faster if on, more transparent if off.");
        
        Image image = IconFactory.getImage("images/toolbar/oneStepSimplifier.png");
        putValue(SMALL_ICON, IconFactory.scaleIcon(image, MainWindow.TOOLBAR_ICON_SIZE, 
                MainWindow.TOOLBAR_ICON_SIZE));

        final boolean oneStepSimplificationOn = 
            ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().oneStepSimplification();
        setSelected(oneStepSimplificationOn);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean b = ((AbstractButton) e.getSource()).isSelected();
	ProofSettings.DEFAULT_SETTINGS.getGeneralSettings()
	        .setOneStepSimplification(b);
	OneStepSimplifier.INSTANCE.refresh(getMediator().getSelectedProof());
    }

}
