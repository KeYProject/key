package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

@SuppressWarnings("serial")
public class RightMouseClickToggleAction extends MainWindowAction {

    public RightMouseClickToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Strategy macro menu on right click");
        setTooltip("If ticked, a right mouse click on the sequent opens the strategy " +
                "macro context menu instead of the taclet menu.");
        setSelected(ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isRightClickMacro());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean sel = isSelected();
        ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setRightClickMacros(sel);
    }
}
