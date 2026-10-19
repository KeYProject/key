/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.IdentityHashMap;
import java.util.Map;
import javafx.scene.control.CheckBox;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF;
import de.uka.ilkd.key.gui.fx.notification.NotificationManagerF.Kind;
import de.uka.ilkd.key.settings.FeatureSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * The "Feature Flags" panel, FX port of {@code FeatureSettingsPanel} (Swing
 * {@code key.ui/settings/FeatureSettingsPanel.java}): a checkbox per registered experimental
 * feature ({@link FeatureSettings.Feature#FEATURES}), re-read on every dialog open and written
 * back on apply; turning a restart-required feature on or off asks the user to reload KeY
 * (Swing FeatureSettingsPanel.java:46-70).
 */
final class FeatureSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    private final Map<FeatureSettings.Feature, CheckBox> checkboxes = new IdentityHashMap<>();

    FeatureSettingsProviderF() {
        setHeaderText("Feature Flags");
        setSubHeaderText("Activate or Deactivate specific experimental features in KeY.");
    }

    @Override
    public String getDescription() {
        return "Feature Flags";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        var fs = ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings();
        // the feature registry is static (the record constructor enrolls every feature), so the
        // rows are built once; the checkbox states are re-read on every dialog open like the
        // Swing original rebuilds its rows (FeatureSettingsPanel.java:33-43)
        if (checkboxes.isEmpty()) {
            for (FeatureSettings.Feature feature : FeatureSettings.Feature.FEATURES) {
                checkboxes.put(feature,
                    addCheckBox(feature.id(), feature.documentation(), fs.isActivated(feature)));
            }
        }
        checkboxes.forEach((feature, checkbox) -> checkbox.setSelected(fs.isActivated(feature)));
        return this;
    }

    @Override
    public void apply(MainWindowF window) {
        var fs = ProofIndependentSettings.DEFAULT_INSTANCE.getFeatureSettings();
        boolean showMessageReloadRequired = false;
        for (var entry : checkboxes.entrySet()) {
            boolean activate = entry.getValue().isSelected();
            FeatureSettings.Feature feature = entry.getKey();
            boolean reloadRequired = feature.restartRequired();
            boolean activeBefore = fs.isActivated(feature);
            if (activate) {
                fs.activate(feature);
            } else {
                fs.deactivate(feature);
            }
            if (activeBefore != fs.isActivated(feature)) {
                showMessageReloadRequired |= reloadRequired;
            }
        }
        if (showMessageReloadRequired) {
            NotificationManagerF.getInstance()
                    .notify("A reload of KeY is required due to changed features.", Kind.INFO);
        }
    }
}
