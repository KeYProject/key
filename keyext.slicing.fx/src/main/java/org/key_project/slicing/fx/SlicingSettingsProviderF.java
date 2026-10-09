/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx;

import javafx.scene.Node;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.settings.InvalidSettingsInputExceptionF;
import de.uka.ilkd.key.gui.fx.settings.SettingsPanelF;
import de.uka.ilkd.key.gui.fx.settings.SettingsProviderF;

import org.key_project.slicing.SlicingSettings;
import org.key_project.slicing.SlicingSettingsProvider;

import org.jspecify.annotations.NullMarked;

/**
 * The proof-slicing options panel, FX port of the Swing
 * {@code org.key_project.slicing.SlicingSettingsProvider} (SlicingSettingsProvider.java:21-120):
 * the "always track" and "aggressive rule de-duplication" toggles plus the graphviz dot
 * executable path, reading and writing the persisted {@link SlicingSettings} of the slicing
 * extension.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> {@code SlicingSettings.setAggressiveDeduplicate} is package-private in
 * {@code org.key_project.slicing} and cannot be called from this module (which may not modify the
 * keyext.slicing sources); the toggle therefore reflects the current setting when the panel is
 * opened, but the FX dialog does not persist changes to it. The other two options persist
 * normally.
 *
 * @author Alexander Weigl
 * @author Arne Keller (port)
 */
@NullMarked
public final class SlicingSettingsProviderF extends SettingsPanelF implements SettingsProviderF {

    /**
     * The settings description shown in the settings dialog tree (Swing
     * {@code SlicingSettingsProvider.getDescription}); also the shared
     * {@link KeYGuiExtensionF.SettingsF} assertion constant of the MP9.4 unit test.
     */
    public static final String DESCRIPTION = "Proof Slicing";

    /**
     * The settings priority (Swing {@code SlicingSettingsProvider.getPriorityOfSettings});
     * also the shared unit-test assertion constant.
     */
    public static final int PRIORITY_OF_SETTINGS = 10000;

    /**
     * Text for introductory explanation (Swing {@code SlicingSettingsProvider.INTRO_LABEL}).
     */
    private static final String INTRO_LABEL = "Adjust proof analysis algorithm options here.";
    /**
     * Label for always track option (Swing {@code SlicingSettingsProvider.ALWAYS_TRACK}).
     */
    private static final String ALWAYS_TRACK = "Always track dependencies";
    /**
     * Explanatory text for always track option (Swing {@code ALWAYS_TRACK_INFO}).
     */
    private static final String ALWAYS_TRACK_INFO = """
            If enabled, the dependency tracker will construct the dependency graph as the proof
            is created. When disabled, the dependency graph is created only when needed, and
            the 'Show proof step that created this formula' action is not available.""";
    /**
     * Label for aggressive deduplicate option (Swing
     * {@code SlicingSettingsProvider.AGGRESSIVE_DEDUPLICATE}).
     */
    private static final String AGGRESSIVE_DEDUPLICATE = "Aggressive rule de-duplication";
    /**
     * Explanatory text for the aggressive de-duplication option (Swing
     * {@code AGGRESSIVE_DEDUPLICATE_INFO}).
     */
    private static final String AGGRESSIVE_DEDUPLICATE_INFO =
        """
                If enabled, the analysis algorithm will de-duplicate more than one duplicate pair at once.
                This may attempt to combine duplicates in impossible ways.
                Disable if you're having trouble slicing a proof using the de-duplication algorithm.""";
    /**
     * Label of the graphviz executable path field (Swing
     * {@code SlicingSettingsProvider.DOT_EXECUTABLE}).
     */
    private static final String DOT_EXECUTABLE = "Graphviz dot executable";
    /**
     * Explanatory text of the graphviz path field (Swing {@code DOT_EXECUTABLE_INFO}).
     */
    private static final String DOT_EXECUTABLE_INFO =
        "Path to dot executable from the graphviz package.";

    /** The "always track" checkbox (Swing {@code SlicingSettingsProvider.alwaysTrack}). */
    private final CheckBox alwaysTrack;
    /**
     * The "aggressive de-duplication" checkbox (Swing
     * {@code SlicingSettingsProvider.aggressiveDeduplicate}).
     */
    private final CheckBox aggressiveDeduplicate;
    /** The dot executable path field (Swing {@code SlicingSettingsProvider.dotExecutable}). */
    private final TextField dotExecutable;

    /**
     * Construct the settings panel (Swing {@code SlicingSettingsProvider} constructor).
     */
    public SlicingSettingsProviderF() {
        setHeaderText("Proof Slicing Options");

        Label intro = new Label(INTRO_LABEL);
        pCenter.add(intro, 0, pCenter.getRowCount(), 3, 1);

        addSeparator("Dependency graph");
        alwaysTrack = addCheckBox(ALWAYS_TRACK, ALWAYS_TRACK_INFO, true);
        dotExecutable = addTextField(DOT_EXECUTABLE, "dot", DOT_EXECUTABLE_INFO, null);

        addSeparator("Duplicate rule applications");
        aggressiveDeduplicate = addCheckBox(AGGRESSIVE_DEDUPLICATE,
            AGGRESSIVE_DEDUPLICATE_INFO, true);
    }

    @Override
    public String getDescription() {
        // Swing SlicingSettingsProvider.getDescription
        return DESCRIPTION;
    }

    @Override
    public Node getPanel(MainWindowF window) {
        // Swing SlicingSettingsProvider.getPanel: re-read the persisted settings
        SlicingSettings ss = SlicingSettingsProvider.getSlicingSettings();
        alwaysTrack.setSelected(ss.getAlwaysTrack());
        dotExecutable.setText(ss.getDotExecutable());
        aggressiveDeduplicate.setSelected(ss.getAggressiveDeduplicate(null));
        return this;
    }

    @Override
    public void apply(MainWindowF window) throws InvalidSettingsInputExceptionF {
        // Swing SlicingSettingsProvider.applySettings
        SlicingSettings ss = SlicingSettingsProvider.getSlicingSettings();
        ss.setAlwaysTrack(alwaysTrack.isSelected());
        ss.setDotExecutable(dotExecutable.getText());
        // KNOWN-SIMPLIFIED: SlicingSettings.setAggressiveDeduplicate(boolean) is package-private
        // in org.key_project.slicing, so this module (which must not modify keyext.slicing)
        // can read the flag but not persist changes made in the dialog.
    }

    @Override
    public int getPriorityOfSettings() {
        // Swing SlicingSettingsProvider.getPriorityOfSettings: sorted last like Swing
        return PRIORITY_OF_SETTINGS;
    }
}
