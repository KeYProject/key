/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Label;
import javafx.scene.control.Spinner;
import javafx.scene.control.Toggle;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * The heatmap options panel, FX port of {@code HeatmapSettingsProvider} (Swing
 * HeatmapExt.java:71-229): the mode radios (no heatmaps / sequent formulae or terms, up to an
 * age or the newest k) and the maximum-age spinner, reading and writing the persisted
 * {@link ViewSettings} heatmap options (HeatmapExt.java:198-223).
 */
final class HeatmapSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    /**
     * Minimal setting for the number of highlighted terms (Swing {@code MIN_AGE}).
     */
    private static final int MIN_AGE = 1;

    /**
     * Maximal setting for the number of highlighted terms (Swing {@code MAX_AGE}).
     */
    private static final int MAX_AGE = 1000;

    /**
     * Text for the introductory heatmap explanation (Swing {@code INTRO_LABEL}).
     */
    private static final String INTRO_LABEL =
        "Heatmaps can be used to highlight the most recent changes in the sequent.";

    /**
     * Explanation for the age spinner (Swing {@code TEXTFIELD_LABEL}).
     */
    private static final String TEXTFIELD_LABEL = "Maximum age of highlighted terms or formulae,"
        + " or number of newest terms or formulae. Please enter a number between " + MIN_AGE
        + " and " + MAX_AGE + ".";

    /**
     * The heatmap highlight modes, mirroring the Swing {@code HeatmapMode} enum of the same
     * name (HeatmapExt.java:106-156).
     */
    enum HeatmapMode {
        DEFAULT("No heatmaps", false, false, false),
        SF_AGE("Sequent formulae up to age", true, true, false),
        SF_NEWEST("Newest sequent formulae", true, true, true),
        TERMS_AGE("Terms up to age", true, false, false),
        TERMS_NEWEST("Newest terms", true, false, true);

        final String text;
        final boolean enableHeatmap;
        final boolean sequent;
        final boolean newest;

        HeatmapMode(String shortText, boolean enableHeatmap, boolean sequent, boolean newest) {
            text = shortText;
            this.enableHeatmap = enableHeatmap;
            this.sequent = sequent;
            this.newest = newest;
        }
    }

    private final javafx.scene.control.ToggleGroup modeGroup;
    private final Spinner<Integer> spinnerAge;

    HeatmapSettingsProviderF() {
        setHeaderText("Heatmap Options");

        Label intro = new Label(INTRO_LABEL);
        intro.setWrapText(true);
        pCenter.add(intro, 0, pCenter.getRowCount(), 3, 1);

        // extension: MP9.0 — Swing HeatmapExt.java:160-184: the five mode radios (with the
        // separator groupings) and the max-age spinner; the FX SettingsPanelF renders one
        // radio group and the spinner rows.
        modeGroup = addRadioButtons("Heatmap Mode", List.of(HeatmapMode.values()),
            TEXTFIELD_LABEL);
        spinnerAge = addIntNumberField("Maximal age:", MIN_AGE, MAX_AGE, 1,
            (int) ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .getMaxAgeForHeatmap(),
            TEXTFIELD_LABEL, null);
        // Swing HeatmapExt.java:181-184: the live-update comment is a no-op in the Swing
        // original as well — the value is written on apply only.
    }

    @Override
    public String getDescription() {
        return "Heatmap";
    }

    @Override
    public javafx.scene.Node getPanel(MainWindowF window) {
        // extension: MP9.0 — Swing HeatmapExt.java:198-210: {@code getPanel} re-reads the
        // ViewSettings and selects the matching mode / spinner value.
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        for (Toggle toggle : modeGroup.getToggles()) {
            Object data = toggle.getUserData();
            if (data instanceof HeatmapMode mode
                    && mode.enableHeatmap == vs.isShowHeatmap()
                    && (!mode.enableHeatmap
                            || (mode.sequent == vs.isHeatmapSF()
                                    && mode.newest == vs.isHeatmapNewest()))) {
                modeGroup.selectToggle(toggle);
                break;
            }
        }
        spinnerAge.getValueFactory().setValue(vs.getMaxAgeForHeatmap());
        return this;
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        // extension: MP9.0 — Swing HeatmapExt.java:213-223: {@code applySettings} writes the
        // selected mode and the spinner value into the ViewSettings.
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        Toggle selected = modeGroup.getSelectedToggle();
        if (selected != null && selected.getUserData() instanceof HeatmapMode mode) {
            vs.setHeatmapOptions(mode.enableHeatmap, mode.sequent, mode.newest,
                Math.clamp(spinnerAge.getValue(), MIN_AGE, MAX_AGE));
        }
    }

    @Override
    public int getPriorityOfSettings() {
        // extension: MP9.0 — Swing HeatmapExt.java:227-229: sorted last like Swing.
        return 10000;
    }
}
