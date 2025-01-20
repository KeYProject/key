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
 * Toggles the tooltips of the source view.
 *
 * @author Wolfram Pfeifer
 *
 * @see de.uka.ilkd.key.gui.sourceview.SourceView#getToolTipText()
 */
public class ToggleSourceViewTooltipAction extends MainWindowAction {
    /** This action's name. */
    public static final String NAME = "Show Tooltips in Source View";

    /** This action's tooltip. */
    public static final String TOOL_TIP = "If ticked, moving the mouse over a term in the"
        + " source view will show a tooltip with additional information.";

    // private static final long serialVersionUID = -3352122484627890921L;

    /** Listens to changes to the view settings to call {@link #updateSelectedState()}. */
    private final PropertyChangeListener viewSettingsListener = e -> updateSelectedState();

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleSourceViewTooltipAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(viewSettingsListener);
        updateSelectedState();
    }

    /**
     * Updates the state of this action according to {@link ViewSettings#isShowSourceViewTooltips()}
     */
    protected void updateSelectedState() {
        final boolean setting =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isShowSourceViewTooltips();
        setSelected(setting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setShowSourceViewTooltips(selected);
    }
}
