package de.uka.ilkd.key.gui.proofExploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowExplorationStepAction;
import de.uka.ilkd.key.proof.Proof;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
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

    private JButton showExplorationSteps;

    /**
     * Combobox for choosing which kind of taclets to apply
     */
    //private JComboBox<String> soundExploration;

    //label if only cuts should be used
    //public final String WHOLE_APPLICATIONS = "Changes with justification branch";
    //labels if not only cuts should be used
    //public final String SIMPLIFFIED_APPLICATIONS = "Changes without justification branch";

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
                    //soundExploration.setEnabled(true);
                    showSecondBranch.setEnabled(true);
                } else if (e.getStateChange() == ItemEvent.DESELECTED) {
                    explorationModeModel.setExplorationModeSelected(false);
                    //soundExploration.setEnabled(true);
                }
            }
        });
        this.add(explorationMode);
        //soundExploration = new JComboBox<>();
        //soundExploration.setToolTipText("Some exploration rules need a justification branch to be sound. Choose whether to see this branch or hide it.");
        //soundExploration.addItem(WHOLE_APPLICATIONS);
        //soundExploration.addItem(SIMPLIFFIED_APPLICATIONS);
        //soundExploration.addItemListener(new ItemListener() {
        /*    @Override
            public void itemStateChanged(ItemEvent e) {
                if(soundExploration.getSelectedItem() == WHOLE_APPLICATIONS){
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
                    showSecondBranch.setEnabled(true);
                } else {
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
                    showSecondBranch.setEnabled(false);
                }
            }
        });*/
        //soundExploration.setEnabled(false);
        //this.add(soundExploration);

        showSecondBranch = new JCheckBox("Show Second Branch");
        showSecondBranch.setToolTipText("Exploration actions are \noften done using a cut. Choose to hide\n " +
                "the second cut-branches from the view \nto focus on the exploration. Uncheck to focus on these branches.");
        showSecondBranch.addItemListener(new ItemListener() {
            @Override
            public void itemStateChanged(ItemEvent e) {
                if(e.getStateChange() == ItemEvent.SELECTED){
                    explorationModeModel.setShowSecondBranches(true);
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
                } else {
                    explorationModeModel.setShowSecondBranches(false);
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.SIMPLIFIED_APP);
                }

            }
        });
        /*if(explorationModeModel.isExplorationModeSelected() && explorationModeModel.getExplorationTacletAppState() == ExplorationModeModel.ExplorationState.WHOLE_APP) {
            showSecondBranch.setEnabled(true);
        } else {
            showSecondBranch.setEnabled(false);
        }*/
        this.add(showSecondBranch);

        this.showExplorationSteps = new JButton(new ShowExplorationStepAction(mw));

        this.add(showExplorationSteps);
        this.setEnabled(true);

    }


}
