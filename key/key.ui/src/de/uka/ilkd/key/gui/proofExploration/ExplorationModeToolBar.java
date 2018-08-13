package de.uka.ilkd.key.gui.proofExploration;

import de.uka.ilkd.key.gui.MainWindow;

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

    private JCheckBox showSecondBranch;

    private ExplorationModeModel explorationModeModel;
    /**
     * Combobox for choosing which kind of taclets to apply
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
    public ExplorationModeToolBar(MainWindow mw, ExplorationModeModel explorationModeModel){
        this.mw = mw;
        this.explorationModeModel = explorationModeModel;
        initialize();
    }


    /**
     * Initialize the toolbar and set the listeners
     */
    private void initialize() {
        this.setName("Exploration Mode Settings");

        explorationMode = new JRadioButton("Exploration Mode");
        explorationMode.setToolTipText("Choose to start ExplorationMode");
        explorationMode.addItemListener(new ItemListener() {
            public void itemStateChanged(ItemEvent e) {
                if (e.getStateChange() == ItemEvent.SELECTED) {
                    explorationModeModel.setExplorationModeSelected(true);
                    soundExploration.setEnabled(true);
                    showSecondBranch.setEnabled(true);
                } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                    explorationModeModel.setExplorationModeSelected(false);
                    soundExploration.setEnabled(false);
                }
            }
        });
        this.add(explorationMode);
        soundExploration = new JComboBox<>();
        soundExploration.setToolTipText("Choose which rules to apply in exploration mode:\n" +
                "Choosing \"sound rules\" only applies sound rules when doing exploration.\n " +
                "This results in almost all the cases in a cut rule application.\n " +
                "Choosing \"unsound\" the sequent can be changed freely and the changes may be unsound.");
        soundExploration.addItem(SOUND_APPLICATIONS);
        soundExploration.addItem(UNSOUND_APPLICATIONS);
        soundExploration.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if(soundExploration.getSelectedItem() == SOUND_APPLICATIONS){
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.SOUND_APPS);
                    showSecondBranch.setEnabled(true);
                } else {
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.UNSOUND_APPS);
                    showSecondBranch.setEnabled(false);
                }
            }
        });
        soundExploration.setEnabled(false);
        this.add(soundExploration);

        showSecondBranch = new JCheckBox("Show Second Branch");
        showSecondBranch.setToolTipText("Exploration actions are \noften done using a cut. Choose to hide\n " +
                "the second cut-branches from the view \nto focus on the exploration. Uncheck to focus on these branches.");
        showSecondBranch.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if(e.getStateChange() == ItemEvent.SELECTED){
                    explorationModeModel.setShowSecondBranches(true);
                } else {
                    explorationModeModel.setShowSecondBranches(false);
                }

            }
        });
        if(explorationModeModel.isExplorationModeSelected() && explorationModeModel.getExplorationTacletAppState() == ExplorationModeModel.ExplorationState.SOUND_APPS) {
            showSecondBranch.setEnabled(true);
        } else {
            showSecondBranch.setEnabled(false);
        }
        this.add(showSecondBranch);
        this.setEnabled(true);

    }


}
