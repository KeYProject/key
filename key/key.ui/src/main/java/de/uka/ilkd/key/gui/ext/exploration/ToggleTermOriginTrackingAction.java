package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.actions.QuickLoadAction;
import de.uka.ilkd.key.gui.actions.QuickSaveAction;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Action to toggle {@link TermLabelSettings#getUseOriginLabels()}.
 *
 * @author lanzinger
 */
public class ToggleTermOriginTrackingAction extends MainWindowAction {

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleTermOriginTrackingAction(MainWindow mainWindow) {
        super(mainWindow);
        setIcon(IconFactory.originIcon());
        setEnabled(true);
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE
                .getTermLabelSettings().getUseOriginLabels());

        putValue(KeYExtConst.PATH, "Origin Tracking");
        setName("Toggle Origin Tracking");
        setTooltip("Track where in the JML specification a every term in the sequent originates.");
        putValue(KeYExtConst.CHECKMARK, true);
    }

    private void handleAction() {
        Proof proof = mainWindow.getMediator().getSelectedProof();
        TermLabelSettings settings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        if (proof != null) {
            Services services = proof.getServices();

            if (!settings.getUseOriginLabels()) {
                for (Proof p : services.getSpecificationRepository().getAllProofs()) {
                    for (Goal g : p.openGoals()) {
                        g.setSequent(OriginTermLabel.removeOriginLabels(g.sequent(), services));
                    }
                }

                services.getSpecificationRepository().map(
                        term -> OriginTermLabel.removeOriginLabels(term, services),
                        services);
            }

            mainWindow.getMediator().getSelectionModel().fireSelectedNodeChanged();
        }
    }

    @Override
    public void actionPerformed(ActionEvent event) {
        TermLabelSettings settings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        if (!settings.getUseOriginLabels()) {
            Object[] options = {
                "Reload",
                "Continue without reloading",
                "Cancel"
            };

            int selection = JOptionPane.showOptionDialog(
                    mainWindow,
                    "Origin information will be added to all newly loaded proofs.\n"
                            + "To see origin information in your current proof, "
                            + "you need to reload it.",
                    "Origin",
                    JOptionPane.DEFAULT_OPTION,
                    JOptionPane.INFORMATION_MESSAGE,
                    null,
                    options,
                    options[2]);

            switch (selection) {
            case 0:
                QuickSaveAction.quickSave(mainWindow);
                QuickLoadAction.quickLoad(mainWindow);
                //fallthrough
            case 1:
                settings.setUseOriginLabels(!settings.getUseOriginLabels());
                handleAction();
            }
        } else {
            Object[] options = {
                "Remove",
                "Cancel"
            };

            int selection = JOptionPane.showOptionDialog(
                    mainWindow,
                    "All origin information will be removed from "
                            + "every open goal and every proof obligation.",
                    "Origin",
                    JOptionPane.DEFAULT_OPTION,
                    JOptionPane.INFORMATION_MESSAGE,
                    null,
                    options,
                    options[1]);

            if (selection == 0) {
                settings.setUseOriginLabels(!settings.getUseOriginLabels());
                handleAction();
            }
        }

        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE
                .getTermLabelSettings().getUseOriginLabels());
    }
}
