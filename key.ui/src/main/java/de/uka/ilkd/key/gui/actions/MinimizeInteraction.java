package de.uka.ilkd.key.gui.actions;

import java.util.EventObject;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

/*
 * Is this a legacy option? Finding instantiations seems to be done by the prover, even if this
 * option is disabled. (Kai Wallisch, December 2013)
 */
public class MinimizeInteraction extends KeYMenuCheckBox {
    public static final String NAME = "Minimize Interaction";
    public static final String TOOL_TIP =
        "If ticked and automated strategy (play button) is used, the prover tries to minimize user interaction, "
            + "e.g., if the prover can find instantiations by itself, it will not ask the user to provide them.";

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
    private final SettingsListener generalSettingsListener = this::handleGeneralSettingsChanged;

    public MinimizeInteraction(MainWindow mainWindow) {
        super(mainWindow, NAME);
        this.mainWindow = mainWindow;
        setName("MinimizeInteractionInstance");
        setTooltip(TOOL_TIP);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .addSettingsListener(generalSettingsListener); // Attention: The listener is never
                                                               // removed, because there is only one
                                                               // MainWindow!
        updateSelectedState();
    }

    protected void updateSelectedState() {
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter());
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
            ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter();
        updateMainWindow(tacletFilter);
    }
}
