package org.key_project.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter;
import org.jetbrains.annotations.NotNull;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

/**
 * The central place to store global information for Proof Exploration.
 * <p>
 * This class holds the data and the state of proof exploration.
 * <p>
 * For every {@link de.uka.ilkd.key.core.KeYMediator} or {@link MainWindow}
 * should only exists one instance.
 *
 * @see ExplorationExtension
 */
public class ExplorationModeModel {
    public static final String PROP_SHOW_SECOND_BRANCH = "showSecondBranches";
    public static final String PROP_EXPLORE_MODE = "exploreModeSelected";
    public static final String PROP_EXPLORE_TACLET_APP_STATE = "exploreTacletAppState";

    private PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /**
     * Mode which rules to use in actions mode
     */
    private @NotNull ExplorationState explorationTacletAppState = ExplorationState.WHOLE_APP;

    /**
     * boolean flag indicating whether actions mode is turned on and special rules are shown to the user
     */
    private boolean explorationModeSelected = false;
    /**
     * Boolean flag whether to show the second branch or not in sound apps
     */
    private boolean showSecondBranches;

    /**
     * Get the state which kind of taclet to use
     */
    public @NotNull ExplorationState getExplorationTacletAppState() {
        return explorationTacletAppState;
    }

    /**
     * Set the state
     *
     * @param explorationTacletAppState
     */
    public void setExplorationTacletAppState(ExplorationState explorationTacletAppState) {
        boolean old = this.explorationModeSelected;
        this.explorationTacletAppState = explorationTacletAppState;
        changeSupport.firePropertyChange(PROP_EXPLORE_TACLET_APP_STATE, old, explorationModeSelected);
    }

    /**
     * Check whether actions mode is selected
     *
     * @return
     */
    public boolean isExplorationModeSelected() {
        return explorationModeSelected;
    }

    /**
     * Set selection of Exploration mode.
     *
     * Triggers a property change event.
     * @see #PROP_EXPLORE_MODE
     */
    public void setExplorationModeSelected(boolean explorationModeSelected) {
        boolean old = this.explorationModeSelected;
        this.explorationModeSelected = explorationModeSelected;
        changeSupport.firePropertyChange(PROP_EXPLORE_MODE, old, explorationModeSelected);
    }

    /**
     * Returns whether the justification branch should be visible.
     */
    public boolean isShowSecondBranches() {
        return showSecondBranches;
    }

    /**
     * Triggers a property change event, and the rerendering of the proof tree.
     *
     * @see #PROP_SHOW_SECOND_BRANCH
     * @see #isShowSecondBranches()
     */
    public void setShowSecondBranches(boolean showSecondBranches) {
        boolean old = this.showSecondBranches;
        this.showSecondBranches = showSecondBranches;
        changeSupport.firePropertyChange(PROP_SHOW_SECOND_BRANCH, old, showSecondBranches);
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

    /**
     * State whether whole application (with shown second branch) or
     * simplified with hidden branch app should be used
     */
    public enum ExplorationState {
        WHOLE_APP, SIMPLIFIED_APP;
    }
}
