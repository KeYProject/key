package de.uka.ilkd.key.gui;

import javax.swing.*;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

/**
 * Button Toolbar for Exploration mode controls
 *
 */
public class ExplorationModeToolBar extends JToolBar {
    MainWindow mw;

    JToggleButton explorationMode;

    JToggleButton soundExploration;

    public ExplorationModeToolBar(MainWindow mw){
        this.mw = mw;
        initialize();
    }

    private void initialize() {
        this.setName("Exploration Mode Settings");
        explorationMode = new JToggleButton("Exploration Mode");
        explorationMode.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                if (e.getStateChange() == ItemEvent.SELECTED) {
                    mw.getMediator().setExplorationModeToggle(true);
                    soundExploration.setEnabled(true);
                } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                    mw.getMediator().setExplorationModeToggle(false);
                    soundExploration.setEnabled(false);
                }
            }
        });
        this.add(explorationMode);
        soundExploration = new JToggleButton("Only Sound Exploration");
        soundExploration.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if (e.getStateChange() == ItemEvent.SELECTED) {
                    //TODO set controls
                } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                    //soundExploration.setText("Unsound Exploration");
                }
            }
        });
        soundExploration.setEnabled(false);
        this.add(soundExploration);

    }
}
