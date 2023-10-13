/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;
import javax.swing.Action;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.actions.QuickLoadAction;
import de.uka.ilkd.key.gui.actions.QuickSaveAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
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
    private static final long serialVersionUID = -2092724865788720558L;

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleTermOriginTrackingAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Toggle Term Origin Tracking");
        setTooltip("Track where in the JML specification a every term in the sequent originates.");
        setIcon(IconFactory.ORIGIN_LABELS.get(MainWindow.TOOLBAR_ICON_SIZE));

        setEnabled(true);
        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());

        setMenuPath("Origin Tracking");
        putValue(Action.LONG_DESCRIPTION, "Toggle Term Origin Tracking");
        putValue(KeyAction.CHECKBOX, true);
        lookupAcceleratorKey();
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

                services.getSpecificationRepository()
                        .map(term -> OriginTermLabel.removeOriginLabels(term, services), services);
            }

            mainWindow.getMediator().getSelectionModel().fireSelectedNodeChanged();
        }
    }

    @Override
    public void actionPerformed(ActionEvent event) {
        TermLabelSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        if (!settings.getUseOriginLabels()) {
            Object[] options = { "Reload", "Continue without reloading", "Cancel" };

            int selection = JOptionPane.showOptionDialog(mainWindow,
                "Origin information will be added to all newly loaded proofs.\n"
                    + "To see origin information in your current proof, "
                    + "you need to reload it.",
                "Origin", JOptionPane.DEFAULT_OPTION, JOptionPane.INFORMATION_MESSAGE, null,
                options, options[2]);

            switch (selection) {
            case 0:
                QuickSaveAction.quickSave(mainWindow);
                QuickLoadAction.quickLoad(mainWindow);
                // fallthrough
            case 1:
                settings.setUseOriginLabels(!settings.getUseOriginLabels());
                handleAction();
            }
        } else {
            Object[] options = { "Remove", "Cancel" };

            int selection = JOptionPane.showOptionDialog(mainWindow,
                "All origin information will be removed from "
                    + "every open goal and every proof obligation.",
                "Origin", JOptionPane.DEFAULT_OPTION, JOptionPane.INFORMATION_MESSAGE, null,
                options, options[1]);

            if (selection == 0) {
                settings.setUseOriginLabels(!settings.getUseOriginLabels());
                handleAction();
            }
        }

        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
    }
}
