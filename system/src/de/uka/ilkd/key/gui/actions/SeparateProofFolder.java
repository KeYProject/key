package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

public class SeparateProofFolder extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 3453843972242689758L;

    public SeparateProofFolder(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("If ticked and proofs are being saved, they are stored in a separate proof folder "+
        "(which is created automatically, if it does not already exist).");
        setName("Separate Proof Folder");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE
                .getGeneralSettings().storesInSeparateProofFolder());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setSeparateProofFolder(b);
    }
}