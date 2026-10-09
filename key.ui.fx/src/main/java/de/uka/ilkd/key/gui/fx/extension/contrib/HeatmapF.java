/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.CheckMenuItem;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ToggleButton;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsManagerF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * The Heatmap extension, FX port of {@code de.uka.ilkd.key.gui.extension.impl.HeatmapExt}
 * (Swing HeatmapExt.java:30-68): a separate "Heatmap" menu with the toggle and the settings
 * actions, a toolbar control and a {@link SettingsProviderF} with the intensity/age options.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing extension renders the actual heat highlight into the
 * proof tree / sequent (HeatmapExt.java:41-62 delegates to the {@code HeatmapToggleAction} /
 * {@code HeatmapSettingsAction}); the FX port is a lightweight hook only — it provides the menu,
 * the toolbar toggle and the persisted {@link ViewSettings} options (the same settings the Swing
 * provider reads/writes, HeatmapExt.java:198-223), while the actual proof-tree heat overlay is
 * deferred to a later milestone.
 */
@KeYGuiExtensionF.Info(name = "Heatmap", optional = true,
    description = "Colorize the formulae on the sequent based on the most recent changes. "
        + "KNOWN-SIMPLIFIED (FX): settings and toggle only — the proof-tree heat overlay is "
        + "deferred.",
    experimental = false)
public class HeatmapF
        implements KeYGuiExtensionF, KeYGuiExtensionF.MainMenuF, KeYGuiExtensionF.ToolbarF,
        KeYGuiExtensionF.SettingsF {

    private final SettingsProviderF heatmapSettingsProvider = new HeatmapSettingsProviderF();

    @Override
    public List<Menu> getMenus(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.0 — Swing HeatmapExt.java:41-51: the main menu holds the toggle and
        // the settings action; the FX SPI contributes whole menus, so the two actions live in a
        // NEW separate "Heatmap" menu (the five built-in menu bars and their item sets stay
        // untouched — key.fx.verify.menuparity keeps asserting 16/24/12/7/5).
        Menu heatmap = new Menu("Heatmap");
        heatmap.getItems().addAll(toggleItem(window), settingsItem(window));
        return List.of(heatmap);
    }

    /**
     * The "Show Heatmap" toggle (Swing {@code HeatmapToggleAction}): switches the persisted
     * {@link ViewSettings} heatmap flag; the checkbox reflects the current flag when the menu
     * is (re)built.
     */
    private MenuItem toggleItem(MainWindowF window) {
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        CheckMenuItem toggle = new CheckMenuItem("Show Heatmap");
        toggle.setSelected(vs.isShowHeatmap());
        toggle.setOnAction(e -> vs.setHeatmapOptions(!vs.isShowHeatmap(), vs.isHeatmapSF(),
            vs.isHeatmapNewest(), vs.getMaxAgeForHeatmap()));
        return toggle;
    }

    /** The "Heatmap Settings…" action (Swing {@code HeatmapSettingsAction}): opens the dialog. */
    private MenuItem settingsItem(MainWindowF window) {
        MenuItem settings = new MenuItem("Heatmap Settings…");
        settings.setOnAction(e -> SettingsManagerF.getInstance()
                .showSettingsDialog(window, heatmapSettingsProvider));
        return settings;
    }

    @Override
    public List<Control> getToolbarControls(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.0 — Swing HeatmapExt.java:54-62: the toolbar holds the toggle button
        // (icon-only in Swing, labelled here) and the settings action.
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        ToggleButton toggle = new ToggleButton("Heatmap");
        toggle.setTooltip(new Tooltip("Toggle the (deferred) heatmap overlay; the option is "
            + "persisted in the ViewSettings."));
        toggle.setSelected(vs.isShowHeatmap());
        toggle.setOnAction(e -> vs.setHeatmapOptions(toggle.isSelected(), vs.isHeatmapSF(),
            vs.isHeatmapNewest(), vs.getMaxAgeForHeatmap()));
        javafx.scene.control.Button settings =
            new javafx.scene.control.Button("Heatmap Settings…");
        settings.setTooltip(new Tooltip("Open the heatmap options in the settings dialog."));
        settings.setOnAction(e -> SettingsManagerF.getInstance()
                .showSettingsDialog(window, heatmapSettingsProvider));
        return List.of(toggle, settings);
    }

    @Override
    public SettingsProviderF getSettings() {
        // extension: MP9.0 — Swing HeatmapExt.java:64-67: {@code getSettings()} returns the
        // heatmap options provider; the host registers it into the SettingsManagerF registry
        // (Swing SettingsManager.registerProvider).
        return heatmapSettingsProvider;
    }
}
