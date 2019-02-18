package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Action to toggle {@link TermLabelSettings#getUseOriginLabels()}.
 *
 * @author lanzinger
 */
public class ToggleOriginLabelsAction extends MainWindowAction {

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleOriginLabelsAction(MainWindow mainWindow) {
        super(mainWindow);
        putValue(KeYExtConst.PATH, "Origin Term Labels");
        setName("Toggle Origin Labels");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Proof proof = mainWindow.getMediator().getSelectedProof();

        if (proof != null) {
            TermLabelSettings settings = proof.getSettings().getTermLabelSettings();
            settings.setUseOriginLabels(!settings.getUseOriginLabels());
        }
    }
}
