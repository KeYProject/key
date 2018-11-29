package de.uka.ilkd.key.gui.proofExploration;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JToggleButton;
import javax.swing.JToolBar;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowExplorationStepAction;

/**
 * Button Toolbar for Exploration mode controls
 *
 * @author Sarah Grebing
 */
public class ExplorationModeToolBar extends JToolBar {

    private static final long serialVersionUID = 2882840652498904204L;

    private MainWindow mw;

    private JToggleButton explorationMode;

    private JToggleButton showSecondBranch;

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

        explorationMode = new JToggleButton("Exploration Mode");

        showSecondBranch = new JToggleButton("Show Second Branch");

        showExplorationSteps = new JButton(new ShowExplorationStepAction(mw));

        showSecondBranch.setEnabled(false);
        showExplorationSteps.setEnabled(false);

        explorationMode.setToolTipText("Choose to start ExplorationMode");

        explorationMode.addActionListener(new ActionListener() {

            boolean active = false;

            @Override
            public void actionPerformed(ActionEvent arg0) {
                active = !active;

                showSecondBranch.setEnabled(active);
                showExplorationSteps.setEnabled(active);

                if (active) {
                    explorationModeModel.setExplorationModeSelected(true);
                    //soundExploration.setEnabled(true);
                    showSecondBranch.setEnabled(true);
                    explorationMode.getModel().setPressed(true);
                } else {
                    explorationModeModel.setExplorationModeSelected(false);
                    explorationMode.getModel().setPressed(false);

                    if (showSecondBranch.getModel().isPressed()) {
                        showSecondBranch.doClick();
                    }
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
        showSecondBranch.setToolTipText("Exploration actions are \noften done using a cut. Choose to hide\n " +
                "the second cut-branches from the view \nto focus on the exploration. Uncheck to focus on these branches.");
        showSecondBranch.addActionListener(new ActionListener() {

            boolean active = false;

            @Override
            public void actionPerformed(ActionEvent arg0) {
                if (MainWindow.getInstance().getProofTreeView().getDelegateModel() == null) {
                    // No proof loaded, so we cannot register the filter.
                    return;
                }

                active = !active;
                explorationModeModel.setShowSecondBranches(active);
                showSecondBranch.getModel().setPressed(active);

                if (active) {
                    explorationModeModel.setExplorationTacletAppState(ExplorationModeModel.ExplorationState.WHOLE_APP);
                } else {
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

        this.add(showExplorationSteps);
        this.setEnabled(true);

    }


}
