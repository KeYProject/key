package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.HeatmapOptionsDialog;
import de.uka.ilkd.key.gui.MainWindow;

public class HeatmapSettingsAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 7840660371360611750L;

    public HeatmapSettingsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Heatmap Options");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        new HeatmapOptionsDialog();
    }

}
