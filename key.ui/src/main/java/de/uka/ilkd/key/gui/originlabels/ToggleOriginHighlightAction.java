/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Action to toggle {@link ViewSettings#isHighlightOrigin()}.
 *
 * @author lanzinger
 */
public class ToggleOriginHighlightAction extends MainWindowAction {
    private static final long serialVersionUID = 9018136291828393238L;

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleOriginHighlightAction(MainWindow mainWindow) {
        super(mainWindow);
        setIcon(IconFactory.ORIGIN_HIGHLIGHT_ICON.get());
        setEnabled(true);
        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHighlightOrigin());

        setMenuPath("Origin Tracking");
        setName("Highlight Origins");
        setTooltip("When moving the mouse over a term in the sequent view,"
            + "highlight its origin in the source view.");
        putValue(KeyAction.CHECKBOX, true);

        ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().addPropertyChangeListener(
            event -> {
                boolean useOriginLabels = ProofIndependentSettings.DEFAULT_INSTANCE
                        .getTermLabelSettings().getUseOriginLabels();

                setEnabled(useOriginLabels);
            });
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean oldValue =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHighlightOrigin();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHighlightOrigin(!oldValue);
    }
}
