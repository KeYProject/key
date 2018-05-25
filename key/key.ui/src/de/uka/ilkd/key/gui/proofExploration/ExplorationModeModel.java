package de.uka.ilkd.key.gui.proofExploration;

public class ExplorationModeModel {
    /**
     * Mode which rules to use in exploration mode
     */
    private ExplorationState ExplorationTacletAppState = ExplorationState.SOUND_APPS;


    /**
     * boolean flag indicating whether exploration mode is turned on and special rules are shown to the user
     */

    private boolean explorationModeSelected = false;

    /**
     * State whether sound or unsound apps should be used
     */
    public enum ExplorationState{
        SOUND_APPS, UNSOUND_APPS;
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
     * Check whether exploration mode is slected
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
    }


}
