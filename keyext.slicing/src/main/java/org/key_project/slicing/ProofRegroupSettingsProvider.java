package org.key_project.slicing;


import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsPanel;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.Pair;

import net.miginfocom.layout.CC;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class ProofRegroupSettingsProvider extends SettingsPanel implements SettingsProvider {
    /**
     * Singleton instance of the settings.
     */
    private static final ProofRegroupSettings SETTINGS = new ProofRegroupSettings();

    /**
     * Text for introductory explanation
     */
    private static final String INTRO_LABEL = "Adjust heuristics groups here.";

    private final List<Pair<String, JTextArea>> groups = new ArrayList<>();

    /**
     * Construct a new settings provider.
     */
    public ProofRegroupSettingsProvider() {
        setHeaderText("Proof Regrouping Options");
    }

    @Override
    public String getDescription() {
        return "Proof Regrouping";
    }

    /**
     * @return the settings managed by this provider
     */
    public static ProofRegroupSettings getSettings() {
        ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(SETTINGS);
        return SETTINGS;
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        ProofRegroupSettings ss = getSettings();

        pCenter.removeAll();
        pCenter.add(new JLabel(INTRO_LABEL), new CC().span().alignX("left"));

        for (var e : ss.getGroups().entrySet()) {
            var ta =
                addTextArea(e.getKey(), String.join("\n", e.getValue()), null, emptyValidator());
            groups.add(new Pair<>(e.getKey(), ta));
        }

        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        ProofRegroupSettings ss = getSettings();
        for (Pair<String, JTextArea> ta : groups) {
            ss.updateGroup(ta.first, List.of(ta.second.getText().split("\n")));
        }
    }


    @Override
    public int getPriorityOfSettings() {
        return 10000;
    }
}
