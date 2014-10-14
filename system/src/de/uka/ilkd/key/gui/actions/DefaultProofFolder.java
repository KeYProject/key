package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;

public class DefaultProofFolder extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 3453843972242689758L;

    public DefaultProofFolder(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("If ticked and proofs are being saved, they are stored in a default proof folder "+
        "(as a sub directory, which is created automatically, if it does not already exist).");
        setName("Default Proof Folder");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                                                  .storesInDefaultProofFolder());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean sel = isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setSeparateProofFolder(sel);
    }
}