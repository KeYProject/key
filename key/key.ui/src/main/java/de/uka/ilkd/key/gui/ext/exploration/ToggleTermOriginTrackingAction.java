package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
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
    public void actionPerformed(ActionEvent e) {
        TermLabelSettings settings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();
        settings.setUseOriginLabels(!settings.getUseOriginLabels());

        handleAction();

        if (settings.getUseOriginLabels()) {
            JOptionPane.showMessageDialog(
                    mainWindow,
                    "Origin information will be added to all newly loaded proofs.\n"
                            + "To see origin information in your current proof, "
                            + "you need to reload it.",
                    "Origin",
                    JOptionPane.INFORMATION_MESSAGE);
        } else {
            JOptionPane.showMessageDialog(
                    mainWindow,
                    "All origin information has been removed from "
                            + "every open goal and every proof obligation.",
                    "Origin",
                    JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
