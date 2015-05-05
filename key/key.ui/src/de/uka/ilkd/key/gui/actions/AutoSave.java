package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class AutoSave extends MainWindowAction {
    
    private static final long serialVersionUID = -2598146925208531491L;
    private static final int DEFAULT_PERIOD = 2000;

    public AutoSave(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Proofs will be automatically saved to +" + IOUtil.getTempDirectory() +
        		"periodically and when finished.");
        setName("Auto Save Proofs");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().autoSavePeriod() > 0);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        int p = isSelected()? DEFAULT_PERIOD: 0;
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setAutoSave(p);
        this.getMediator().setAutoSave(p);
    }

}
