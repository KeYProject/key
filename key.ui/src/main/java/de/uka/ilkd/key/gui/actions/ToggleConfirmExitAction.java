package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

public class ToggleConfirmExitAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 3453843972242689758L;

    public ToggleConfirmExitAction(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Ask for extra confirmation when trying to exit the prover");
        setName("Confirm Exit");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().confirmExit());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean b = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setConfirmExit(b);
    }

}
