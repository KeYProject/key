package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class RightMouseClickToggleAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 1299838459448346807L;

    public RightMouseClickToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Right Click for Proof Macros");
        setTooltip("If ticked, a right click on the sequent opens the strategy macro context menu");
        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro());
        // setSelected(ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isRightClickMacro());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean sel = isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setRightClickMacros(sel);
        // ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().setRightClickMacros(sel);
    }
}
