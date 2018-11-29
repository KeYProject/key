package de.uka.ilkd.key.gui.proofExploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter;

public class ExplorationModeModel {



    /**
     * Mode which rules to use in exploration mode
     */
    private ExplorationState ExplorationTacletAppState = ExplorationState.WHOLE_APP;


    /**
     * boolean flag indicating whether exploration mode is turned on and special rules are shown to the user
     */

    private boolean explorationModeSelected = false;

    /**
     * State whether whole application (with shown second branch) or simplified with hidden branch app should be used
     */
    public enum ExplorationState{
        WHOLE_APP, SIMPLIFIED_APP;
    }


    /**
     * Boolean flag whether to show the second branch or not in sound apps
     */
    private boolean showSecondBranches;
    /**
     * Get the state which kind of taclet to use
     * @return
     */
    public ExplorationState getExplorationTacletAppState() {
        return ExplorationTacletAppState;
    }

    /**
     * Set the state
     * @param explorationTacletAppState
     */
    public void setExplorationTacletAppState(ExplorationState explorationTacletAppState) {
        ExplorationTacletAppState = explorationTacletAppState;
    }

    /**
     * Check whether exploration mode is selected
     * @return
     */
    public boolean isExplorationModeSelected() {
        return explorationModeSelected;
    }

    /**
     * Set selection of Exploration mode
     * @param explorationModeSelected
     */
    public void setExplorationModeSelected(boolean explorationModeSelected) {
        this.explorationModeSelected = explorationModeSelected;
    }

    /**
     * Request selection
     * @return
     */
    public boolean isShowSecondBranches() {
        return showSecondBranches;
    }

    /**
     * Set selection
     * @param showSecondBranches
     */
    public void setShowSecondBranches(boolean showSecondBranches) {
        this.showSecondBranches = showSecondBranches;

        GUIProofTreeModel delegateModel =
                MainWindow.getInstance().getProofTreeView().getDelegateModel();

        delegateModel.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS, showSecondBranches);
    }


}
