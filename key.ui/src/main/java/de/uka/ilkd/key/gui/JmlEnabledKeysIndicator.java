package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import javax.swing.*;
import java.util.List;

/**
 * Provides a Label in the status line for the indication of the current enabled keys for the JML condition evaluation.
 * @author weigl
 * @see GeneralSettings#getJmlEnabledKeys()
 */
@KeYGuiExtension.Info(experimental = false, name = "JML Enabled Keys Indicator for the Status Line")
public class JmlEnabledKeysIndicator implements KeYGuiExtension, KeYGuiExtension.StatusLine {
    private final GeneralSettings settings = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
    private final JLabel lblIndicator = new JLabel();

    public JmlEnabledKeysIndicator() {
        lblIndicator.setToolTipText("Current enabled keys for the JML condition evaluation");
        settings.addPropertyChangeListener(GeneralSettings.KEY_JML_ENABLED_KEYS, it -> update());
        update();
    }

    private void update() {
        var lbl = String.join(", ", settings.getJmlEnabledKeys());
        lblIndicator.setText(lbl);
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        return List.of(lblIndicator);
    }
}