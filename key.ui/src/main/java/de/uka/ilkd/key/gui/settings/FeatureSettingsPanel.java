/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.util.IdentityHashMap;
import java.util.Map;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * @author Alexander Weigl
 * @version 1 (04.12.23)
 */
public class FeatureSettingsPanel extends SettingsPanel implements SettingsProvider {
    private final Map<FeatureSettings.Feature, JCheckBox> checkboxes = new IdentityHashMap<>();

    public FeatureSettingsPanel() {
        setHeaderText("Feature Flags");
        setSubHeaderText("Activate or Deactivate specific experimental features in KeY.");
    }

    @Override
    public String getDescription() {
        return "Feature Flags";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        pCenter.removeAll(); // start fresh
        checkboxes.clear();
        var fs = ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings();
        for (FeatureSettings.Feature feature : FeatureSettings.Feature.FEATURES) {
            var cb =
                addCheckBox(feature.id(), feature.documentation(), fs.isActivated(feature), null);
            checkboxes.put(feature, cb);
        }
        return this;
    }

    @Override
    public void applySettings(MainWindow window) throws InvalidSettingsInputException {
        var fs = ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings();
        var showMessageReloadRequired = false;
        for (var entry : checkboxes.entrySet()) {
            var activate = entry.getValue().isSelected();
            var feature = entry.getKey();
            var reloadRequired = feature.restartRequired();
            final var activeBefore = fs.isActivated(feature);

            if (activate)
                fs.activate(feature);
            else
                fs.deactivate(feature);

            final var activeAfter = fs.isActivated(feature);
            if (activeBefore != activeAfter) {
                showMessageReloadRequired |= reloadRequired;
            }
        }

        if (showMessageReloadRequired) {
            JOptionPane.showMessageDialog(this,
                "A reload of KeY is required due to changed features.");
        }
    }
}
