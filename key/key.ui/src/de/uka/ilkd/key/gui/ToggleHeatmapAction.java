package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class ToggleHeatmapAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -2210220264094783747L;

    public ToggleHeatmapAction(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Highlight the most recenttly generated sequent formulae");
        setName("Enable Heatmap");
                setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHeatmapEnabled());
    }
    
    @Override
    public void actionPerformed(ActionEvent e) {
        boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().enableHeatmap(b);
    }
}
