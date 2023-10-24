/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.actions.QuickLoadAction;
import de.uka.ilkd.key.gui.actions.QuickSaveAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
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

    @Override
    public void actionPerformed(ActionEvent event) {
        TermLabelSettings settings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        Object[] options = { "Reload", "Continue without reloading", "Cancel" };

        int selection = JOptionPane.showOptionDialog(mainWindow,
            "For the change to take effect, you need to reload the proof.",
            "Origin", JOptionPane.DEFAULT_OPTION, JOptionPane.INFORMATION_MESSAGE, null,
            options, options[2]);

        if (selection == JOptionPane.OK_OPTION) {
            QuickSaveAction.quickSave(mainWindow);
            QuickLoadAction.quickLoad(mainWindow);
        }
        settings.setUseOriginLabels(!settings.getUseOriginLabels());

        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().getUseOriginLabels());
    }
}
