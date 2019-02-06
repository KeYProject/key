package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;

/**
 * Saves the currently selected proof as a zip archive with file extension "zproof".
 * The bundle contains all files needed to successfully reload the proof.
 *
 * @author Wolfram Pfeifer
 */
public final class SaveBundleAction extends MainWindowAction {

    public SaveBundleAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Save Bundle");
        // TODO: add own icon 
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof as a bundle.");
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            // Try to save back to file where proof was initially loaded from
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            mainWindow.getUserInterface().saveProofBundle(selectedProof);
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}
