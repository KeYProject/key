package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.configuration.ProofSettings;

@SuppressWarnings("serial")
public class RightMouseClickToggleAction extends MainWindowAction {

    public RightMouseClickToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Right click for macros");
        setTooltip("If ticked, a right click on the sequent opens the strategy macro context menu");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro());
//        setSelected(ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isRightClickMacro());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean sel = isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setRightClickMacros(sel);
//        ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setRightClickMacros(sel);
    }
}
