/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;
import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Toggles the tooltips on the sequent view.
 *
 * @author lanzinger
 *
 * @see SequentView#getToolTipText()
 * @see KeYTooltipExtension
 */
public class ToggleSequentViewTooltipAction extends MainWindowAction {
    /** This action's name. */
    public static final String NAME = "Show Tooltips in Sequent View";

    /** This action's tooltip. */
    public static final String TOOL_TIP = "If ticked, moving the mouse over a term in the"
        + " sequent view will show a tooltip with additional information.";

    private static final long serialVersionUID = -3352122484627890921L;

    /** Listens to changes to the view settings to call {@link #updateSelectedState()}. */
    private final PropertyChangeListener viewSettingsListener = e -> updateSelectedState();

    /**
     * Crate a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleSequentViewTooltipAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .addPropertyChangeListener(viewSettingsListener);
        updateSelectedState();
    }

    /**
     * Updates the state of this action according to
     * {@link ViewSettings#isShowSequentViewTooltips()}
     */
    protected void updateSelectedState() {
        final boolean setting =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isShowSequentViewTooltips();
        setSelected(setting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setShowSequentViewTooltips(selected);
    }
}
