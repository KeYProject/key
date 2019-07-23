package org.key_project.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

public class ExplorationModeModel {
    public static final String PROP_SHOWSECONDBRANCH = "showSecondBranches";
    public static final String PROP_EXPLORE_MODE = "exploreModeSelected";
    public static final String PROP_EXPLORE_TACLET_APP_STATE = "exploreTacletAppState";

    private PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /**
     * Mode which rules to use in actions mode
     */
    private ExplorationState explorationTacletAppState = ExplorationState.WHOLE_APP;

    /**
     * boolean flag indicating whether actions mode is turned on and special rules are shown to the user
     */
    private boolean explorationModeSelected = false;

    /**
     * State whether whole application (with shown second branch) or
     * simplified with hidden branch app should be used
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
        return explorationTacletAppState;
    }

    /**
     * Set the state
     * @param explorationTacletAppState
     */
    public void setExplorationTacletAppState(ExplorationState explorationTacletAppState) {
        boolean old = this.explorationModeSelected;
        this.explorationTacletAppState = explorationTacletAppState;
        changeSupport.firePropertyChange(PROP_EXPLORE_TACLET_APP_STATE, old, explorationModeSelected);
    }

    /**
     * Check whether actions mode is selected
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
        boolean old = this.explorationModeSelected;
        this.explorationModeSelected = explorationModeSelected;
        changeSupport.firePropertyChange(PROP_EXPLORE_MODE, old, explorationModeSelected);
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
        boolean old = this.showSecondBranches;
        this.showSecondBranches = showSecondBranches;
        changeSupport.firePropertyChange(PROP_SHOWSECONDBRANCH, old, showSecondBranches);

        GUIProofTreeModel delegateModel =
                MainWindow.getInstance().getProofTreeView().getDelegateModel();

        delegateModel.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS, showSecondBranches);
    }

    public void addPropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(listener);
    }

    public void removePropertyChangeListener(PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(listener);
    }

    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.addPropertyChangeListener(propertyName, listener);
    }

    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        changeSupport.removePropertyChangeListener(propertyName, listener);
    }
}
