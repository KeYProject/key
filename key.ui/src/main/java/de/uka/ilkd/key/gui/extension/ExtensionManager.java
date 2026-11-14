/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.extension;

import java.awt.*;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.impl.Extension;
import de.uka.ilkd.key.gui.extension.impl.ExtensionSettings;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.help.HelpFacade;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import net.miginfocom.layout.CC;
import org.jspecify.annotations.NullMarked;

/**
 * Settings panel where extensions are disabled / enabled.
 *
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
@NullMarked
public class ExtensionManager extends SettingsPanel implements SettingsProvider {
    private static final ExtensionSettings EXTENSION_SETTINGS = new ExtensionSettings();
    private HashMap<JCheckBox, Extension<?>> map = new HashMap<>();
    private String keywords = "";

    /**
     * Creates the extension settings panel.
     *
     * <p>
     * The panel sets its header texts and rebuilds its extension list while the receiver is still
     * under initialization (EISOP initialization check); the settings only materialize once the
     * panel is shown after construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ExtensionManager() {
        setHeaderText("Extension Settings");
        setSubHeaderText("Settings will be applied on next restart");
        lblSubhead.setIcon(IconFactory.WARNING_INCOMPLETE.get());
        lblSubhead.setBackground(Color.orange.darker());

        JLabel lblExplainExperimental =
            new JLabel("<html>The flask marks extensions " + "that are only available, <br>"
                + "if KeY was started in experimental mode. Restart KeY with `--experimental`.");
        lblExplainExperimental.setIcon(IconFactory.EXPERIMENTAL_EXTENSION.get());
        pNorth.add(lblExplainExperimental);

        refresh();
    }

    public static ExtensionSettings getExtensionSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(EXTENSION_SETTINGS);
        return EXTENSION_SETTINGS;
    }

    private void refresh() {
        pCenter.removeAll();
        map = new HashMap<>();
        keywords = "";
        keywords += lblHead.getText();

        keywords += lblSubhead.getText();

        KeYGuiExtensionFacade.getExtensions().stream()
                .sorted(Comparator.comparingInt(
                    it -> it.isDisabledByMaintainer() || !it.isOptional() ? 1 : 0))
                .filter(it -> !it.isDisabledByMaintainer()).forEach(it -> {
                    JCheckBox box = new JCheckBox();
                    box.setText(it.getName());
                    box.setSelected(!it.isDisabled());
                    box.setEnabled(it.isOptional());
                    map.put(box, it);

                    keywords += box.getText();

                    JLabel experimentalLabel = new JLabel();
                    if (it.isExperimental()) {
                        experimentalLabel.setIcon(IconFactory.EXPERIMENTAL_EXTENSION.get());
                    }
                    pCenter.add(experimentalLabel, new CC().newline());
                    pCenter.add(box);

                    JLabel lblProvides = new JLabel(getSupportLabel(it));
                    keywords += lblProvides.getText();
                    Font providesFont = lblProvides.getFont();
                    if (providesFont == null) {
                        // a newly created label is never realized without a font
                        throw new NullPointerException("No label font available.");
                    }
                    lblProvides.setFont(providesFont.deriveFont(Font.ITALIC));
                    pCenter.add(new JLabel(), new CC().newline());
                    pCenter.add(lblProvides);

                    if (!it.getDescription().isEmpty()) {
                        pCenter.add(new JLabel(), new CC().newline());
                        pCenter.add(createInfoArea(it.getDescription()));
                        keywords += it.getDescription();
                    }

                    // add a help button if the relevant annotation is there
                    var help = it.getType().getAnnotation(HelpInfo.class);
                    var helpPath = help != null ? help.path() : null;
                    if (helpPath != null) {
                        var infoButton = createHelpButton(() -> HelpFacade.openHelp(helpPath));
                        pCenter.add(infoButton);
                    }
                });
    }

    private String getSupportLabel(Extension<?> it) {
        return "Provides: " + (it.supportsContextMenu() ? "ContextMenu " : "")
            + (it.supportsLeftPanel() ? "LeftPanel " : "")
            + (it.supportsMainMenu() ? "MainMenu " : "")
            + (it.supportsSettings() ? "Settings " : "")
            + (it.supportsStatusLine() ? "StatusLine " : "")
            + (it.supportsToolbar() ? "Toolbar " : "");
    }

    @Override
    public String getDescription() {
        return "Extensions";
    }

    @Override
    public JPanel getPanel(MainWindow window) {
        refresh();
        return this;
    }

    @Override
    public boolean contains(String substring) {
        return keywords.toLowerCase().contains(substring.toLowerCase());
    }

    @Override
    public void applySettings(MainWindow window) {
        Set<String> seq = new HashSet<>();
        map.forEach((k, v) -> {
            if (!k.isSelected()) {
                seq.add(v.getType().getName());
            }
        });
        getExtensionSettings().setForbiddenClasses(seq);
    }
}
