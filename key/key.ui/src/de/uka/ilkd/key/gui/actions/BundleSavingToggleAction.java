package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Toggles the option to save proofs as bundle.
 *
 * @author Wolfram Pfeifer
 */
public class BundleSavingToggleAction extends MainWindowAction {

    /**
     * Creates a new BundleSavingToggleAction.
     * @param mainWindow the main window of the program
     */
    public BundleSavingToggleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Allow proof bundle saving");
        setTooltip("If ticked, a proofs can be saved as bundles"
                + " (at the cost of storing copies of loaded files in a temporary directory).");
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE
                                            .getGeneralSettings()
                                            .isAllowBundleSaving());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE
                                .getGeneralSettings()
                                .setAllowBundleSaving(selected);
    }
}
