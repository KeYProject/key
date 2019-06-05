package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.EventObject;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

public class ToggleSequentViewTooltipAction extends MainWindowAction {

    public static final String NAME = "Show tooltips in sequent view";

    public static final String TOOL_TIP = "If ticked, moving the mouse over a term in the"
            + " sequent view will show a tooltip with additional information.";

    /**
     * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
     * <p>
     * Such changes can occur in the Eclipse context when settings are changed in for instance the KeYIDE.
     */
    private final SettingsListener viewSettingsListener = new SettingsListener() {
        @Override
        public void settingsChanged(EventObject e) {
            handleViewSettingsChanged(e);
        }
    };

    public ToggleSequentViewTooltipAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
            .addSettingsListener(viewSettingsListener);
        updateSelectedState();
    }

    protected void updateSelectedState() {
        final boolean setting = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .isShowSequentViewTooltips();
        setSelected(setting);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean selected = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
            .setShowSequentViewTooltips(selected);
    }

    protected void handleViewSettingsChanged(EventObject e) {
        updateSelectedState();
    }
}
