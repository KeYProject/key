/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;


import java.beans.PropertyChangeListener;
import java.util.EventObject;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Option to specify all instantiations manually (does not apply to the automatic solver).
 */
public class MinimizeInteraction extends KeYMenuCheckBox {
    public static final String NAME = "Minimize Interaction";
    public static final String TOOL_TIP =
        "If not ticked, applying a taclet manually will require you to instantiate " +
            "all schema variables.";

    /**
     *
     */
    private static final long serialVersionUID = -3381517803006651928L;
    private final MainWindow mainWindow;

    /**
     * Listens for changes on
     * {@code ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the
     * KeYIDE.
     */
    private final PropertyChangeListener generalSettingsListener =
        this::handleGeneralSettingsChanged;

    public MinimizeInteraction(MainWindow mainWindow) {
        super(mainWindow, NAME);
        this.mainWindow = mainWindow;
        setName("MinimizeInteractionInstance");
        setTooltip(TOOL_TIP);
        // Attention: The listener is never// removed, because there is only one
        // MainWindow!
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .addPropertyChangeListener(generalSettingsListener);
        updateSelectedState();
    }

    protected void updateSelectedState() {
        setSelected(
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().getTacletFilter());
    }

    @Override
    public void handleClickEvent() {
        boolean tacletFilter = isSelected();
        updateMainWindow(tacletFilter);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .setTacletFilter(tacletFilter);
    }

    protected void updateMainWindow(boolean b) {
        mainWindow.getUserInterface().getProofControl().setMinimizeInteraction(b);
    }

    protected void handleGeneralSettingsChanged(EventObject e) {
        updateSelectedState();
        final boolean tacletFilter =
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().getTacletFilter();
        updateMainWindow(tacletFilter);
    }
}
