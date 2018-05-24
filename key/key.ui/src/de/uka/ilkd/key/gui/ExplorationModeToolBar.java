package de.uka.ilkd.key.gui;

import javax.swing.*;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

/**
 * Button Toolbar for Exploration mode controls
 *
 * @author Sarah Grebing
 */
public class ExplorationModeToolBar extends JToolBar {
    private MainWindow mw;

    private JRadioButton explorationMode;

    private ExplorationState ExplorationTacletAppState = ExplorationState.SOUND_APPS;

    public boolean isExplorationModeSelected() {
        return explorationModeSelected;
    }

    /**
     * boolean flag indicating whether exploration mode is turned on and special rules are shown to the user
     */

    private boolean explorationModeSelected = false;

    /**
     * Cobobox for choosing which kind of taclets to apply
     */
    private JComboBox<String> soundExploration;

    //label if only cuts should be used
    public final String SOUND_APPLICATIONS = "Only sound changes";
    //labels if not only cuts should be used
    public final String UNSOUND_APPLICATIONS = "Allow unsound changes";

    /**
     * Create Explorationmode Toolbar
     * @param mw
     */
    public ExplorationModeToolBar(MainWindow mw){
        this.mw = mw;
        initialize();
    }

    public ExplorationState getExplorationTacletAppState() {
        return ExplorationTacletAppState;
    }

    public void setExplorationTacletAppState(ExplorationState explorationTacletAppState) {
        ExplorationTacletAppState = explorationTacletAppState;
    }

    private void initialize() {
        this.setName("Exploration Mode Settings");

        explorationMode = new JRadioButton("Exploration Mode");
        explorationMode.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                if (e.getStateChange() == ItemEvent.SELECTED) {
                    explorationModeSelected = true;
                    mw.getMediator().setExplorationModeSelected(true);
                    soundExploration.setEnabled(true);
                } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                    explorationModeSelected = false;
                    mw.getMediator().setExplorationModeSelected(false);
                    soundExploration.setEnabled(false);
                }
            }
        });
        this.add(explorationMode);
        soundExploration = new JComboBox<>();
        soundExploration.addItem(SOUND_APPLICATIONS);
        soundExploration.addItem(UNSOUND_APPLICATIONS);
        soundExploration.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if(soundExploration.getSelectedItem().equals(SOUND_APPLICATIONS)){
                    setExplorationTacletAppState(ExplorationState.SOUND_APPS);
                } else {
                    setExplorationTacletAppState(ExplorationState.UNSOUND_APPS);
                }
            }
        });
        soundExploration.setEnabled(false);
        this.add(soundExploration);
        this.setEnabled(true);

    }

    public enum ExplorationState{
        SOUND_APPS, UNSOUND_APPS;
    }
}
