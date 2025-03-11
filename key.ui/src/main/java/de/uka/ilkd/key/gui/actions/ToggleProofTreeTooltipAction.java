/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Toggles the tooltips of the proof tree.
 *
 * @author Wolfram Pfeifer
 */
public class ToggleProofTreeTooltipAction extends MainWindowAction {
    /** This action's name. */
    public static final String NAME = "Show Tooltips in Proof Tree";

    /** This action's tooltip. */
    public static final String TOOL_TIP = "If ticked, moving the mouse over a node in the proof"
        + " tree will show a tooltip with additional information.";

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleProofTreeTooltipAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOL_TIP);
        // Listens to changes to the view settings to call {@link #updateSelectedState()}.
        PropertyChangeListener viewSettingsListener = e -> updateSelectedState();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(viewSettingsListener);
        updateSelectedState();
    }

    /**
     * Updates the state of this action according to {@link ViewSettings#isShowProofTreeTooltips()}
     */
    protected void updateSelectedState() {
        final boolean setting =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isShowProofTreeTooltips();
        setSelected(setting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setShowProofTreeTooltips(selected);
    }
}
