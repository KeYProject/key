/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Provides a Label in the status line for the indication of the current enabled keys for the JML
 * condition evaluation.
 *
 * @author weigl
 * @see GeneralSettings#getJmlEnabledKeys()
 */
@KeYGuiExtension.Info(experimental = false, name = "JML Enabled Keys Indicator for the Status Line")
public class JmlEnabledKeysIndicator implements KeYGuiExtension, KeYGuiExtension.StatusLine {
    private final GeneralSettings settings =
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
    private final JLabel lblIndicator = new JLabel();

    public JmlEnabledKeysIndicator() {
        lblIndicator.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        lblIndicator.setToolTipText("Currently enabled keys for the JML condition evaluation");
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
