/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.HeatmapSettingsAction;
import de.uka.ilkd.key.gui.actions.HeatmapToggleAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import net.miginfocom.layout.CC;

/**
 * Extension adapter for Heatmap
 *
 * @author Alexander Weigl
 */
@KeYGuiExtension.Info(name = "Heatmap", optional = true,
    description = "Colorize the formulae on the sequence based on the most recent changes\n"
        + "Developer: Jonas Schiffl <jonas.schiffl@kit.edu>",
    experimental = false)
public class HeatmapExt implements KeYGuiExtension, KeYGuiExtension.MainMenu,
        KeYGuiExtension.Toolbar, KeYGuiExtension.Settings {
    private final List<Action> actions = new ArrayList<>(2);
    private HeatmapToggleAction toggleAction;
    private HeatmapSettingsAction settingsAction;

    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        return getActions(mainWindow);
    }

    private List<Action> getActions(MainWindow mainWindow) {
        if (actions.isEmpty()) {
            actions.add(toggleAction = new HeatmapToggleAction(mainWindow));
            actions.add(settingsAction = new HeatmapSettingsAction(mainWindow));
        }
        return actions;
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        getActions(mainWindow);// initialize
        JToolBar tb = new JToolBar("Heatmap Options");
        JToggleButton comp = new JToggleButton(toggleAction);
        comp.setHideActionText(true);
        tb.add(comp);
        tb.add(settingsAction);
        return tb;
    }

    @Override
    public SettingsProvider getSettings() {
        return new HeatmapSettingsProvider();
    }
}


/**
 * This Dialog contains options for highlighting sequent formulae or terms according to their age,
 * i.e., when they were first introduced into the proof. It is possible to highlight all sf/terms up
 * to a specified age, or to highlight the x newest sf/terms, x being specified by the user.
 *
 * @author weigl, jschiffl
 */
class HeatmapSettingsProvider extends SettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = 7783431483026950930L;

    /**
     * Minimal setting for number of highlighted terms
     */
    private static final int MIN_AGE = 1;

    /**
     * Maximal setting for number of highlighted terms
     */
    private static final int MAX_AGE = 1000;

    /**
     * Text for introductory heatmap explanation
     */
    private static final String INTRO_LABEL =
        "Heatmaps can be used to " + "highlight the most recent changes in the sequent.";

    /**
     * Explanation for age textfield
     */
    private static final String TEXTFIELD_LABEL = "Maximum age of highlighted \n"
        + "terms or formulae, or number of newest terms or formulae\n"
        + "Please enter a number between " + MIN_AGE + " and " + MAX_AGE + ".";

    private final JSpinner spinnerAge;

    enum HeatmapMode {
        DEFAULT("No heatmaps", "No heatmaps are shown.", false, false, false),
        SF_AGE("Sequent formulae up to age",
                "All sequent formulae that have been added or changed in the last k steps are highlighted. \n"
                    + "More recent formulae will have a stronger highlight. It is possible that less \n"
                    + "than k formulae are highlighted, e.g. if one formula has changed multiple times.\n",
                true, true, false),
        SF_NEWEST("Newest sequent formulae",
                "All formulae in the sequent are sorted by how new they are, i.e., how recently they have\n"
                    + " been added or changed. The first k formulae of the sorted list are highlighted\n"
                    + "according to their position in the list,\n"
                    + " with the most recent formula receiving the strongest highlight.\n",
                true, true, true),
        TERMS_AGE("Terms up to age",
                "All terms that have been added or changed in the last k steps are highlighted. \n"
                    + "More recent terms will have a stronger highlight. It is possible that less than \n"
                    + "k terms are highlighted, e.g. if one term has changed multiple times.",
                true, false, false),
        TERMS_NEWEST("Newest terms",
                "All terms in the sequent are sorted by how new they are, i.e., how recently they\n"
                    + "have been added or changed. The first k terms of the sorted list are highlighted\n"
                    + "according to their position in the list,\n"
                    + " with the most recent term receiving the strongest highlight.",
                true, false, true);

        final String text;
        final String desc;
        final boolean enableHeatmap;
        final boolean sequent;
        final boolean newest;


        HeatmapMode(String shortText, String description, boolean enableHeatmap, boolean sequent,
                boolean newest) {
            desc = description;
            text = shortText;
            this.enableHeatmap = enableHeatmap;
            this.sequent = sequent;
            this.newest = newest;
        }

        public String description() {
            return desc;
        }
    }

    private final Map<HeatmapMode, JRadioButton> map = new HashMap<>();

    HeatmapSettingsProvider() {
        setHeaderText("Heatmap Options");

        ButtonGroup group = new ButtonGroup();
        for (HeatmapMode m : HeatmapMode.values()) {
            JRadioButton radio = new JRadioButton(m.text);
            radio.setActionCommand(m.name());
            group.add(radio);
            map.put(m, radio);
        }
        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        addSeparator("Disable heatmaps");
        addRadio(HeatmapMode.DEFAULT);
        addSeparator("Highlight sequent formulae");
        addRadio(HeatmapMode.SF_AGE);
        addRadio(HeatmapMode.SF_NEWEST);
        addSeparator("Highlight terms");
        addRadio(HeatmapMode.TERMS_AGE);
        addRadio(HeatmapMode.TERMS_NEWEST);

        spinnerAge = addNumberField("Maximal age:", MIN_AGE, MAX_AGE, 1, TEXTFIELD_LABEL, e -> {
            // LIVE UPDATE: VS.setHeatmapOptions(VS.isShowHeatmap(), VS.isHeatmapSF(),
            // VS.isHeatmapNewest(), (int) valueSpinner.getValue()));
        });
    }

    private void addRadio(HeatmapMode mode) {
        JRadioButton radio = map.get(mode);
        addRowWithHelp(mode.desc, new JLabel(), radio);
    }

    @Override
    public String getDescription() {
        return "Heatmap";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        final ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        for (Map.Entry<HeatmapMode, JRadioButton> entry : map.entrySet()) {
            HeatmapMode mode = entry.getKey();
            if (mode.enableHeatmap == vs.isShowHeatmap() && (!mode.enableHeatmap
                    || (mode.sequent == vs.isHeatmapSF() && mode.newest == vs.isHeatmapNewest()))) {
                entry.getValue().setSelected(true);
                break;
            }
        }
        spinnerAge.setValue(vs.getMaxAgeForHeatmap());
        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        final ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        for (Map.Entry<HeatmapMode, JRadioButton> entry : map.entrySet()) {
            if (entry.getValue().isSelected()) {
                HeatmapMode mode = entry.getKey();
                vs.setHeatmapOptions(mode.enableHeatmap, mode.sequent, mode.newest,
                    (int) spinnerAge.getValue());
                break;
            }
        }
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
