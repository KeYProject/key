/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.gui.prooftree.ProofTreeViewFilter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * The central place to store global information for Proof Exploration.
 * <p>
 * This class holds the data and the state of proof exploration.
 * <p>
 * For every {@link de.uka.ilkd.key.core.KeYMediator} or {@link MainWindow} should only exists one
 * instance.
 *
 * @see ExplorationExtension
 */
public class ExplorationModeModel {

    public static final String PROP_EXPLORE_MODE = "exploreModeSelected";
    public static final String PROP_EXPLORE_TACLET_APP_STATE = "exploreTacletAppState";

    private final Map<Proof, AtomicInteger> taintedProofs = new WeakHashMap<>();

    private final PropertyChangeSupport changeSupport = new PropertyChangeSupport(this);

    /**
     * Mode which rules to use in actions mode Default: whole application is shown
     */
    private @Nonnull ExplorationState explorationTacletAppState = ExplorationState.WHOLE_APP;


    /**
     * boolean flag indicating whether actions mode is turned on and special rules are shown to the
     * user
     */
    private boolean explorationModeSelected = false;

    /**
     * Get the state which kind of taclet to use
     */
    public @Nonnull ExplorationState getExplorationTacletAppState() {
        return explorationTacletAppState;
    }

    /**
     * Set the state
     */
    public void setExplorationTacletAppState(ExplorationState explorationTacletAppState) {
        boolean old = this.explorationModeSelected;
        this.explorationTacletAppState = explorationTacletAppState;
        changeSupport.firePropertyChange(PROP_EXPLORE_TACLET_APP_STATE, old,
            explorationModeSelected);
    }

    /**
     * Check whether actions mode is selected
     */
    public boolean isExplorationModeSelected() {
        return explorationModeSelected;
    }

    /**
     * Set selection of Exploration mode.
     *
     * Triggers a property change event.
     *
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
    public boolean isShowInteractiveBranches() {
        return !ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .getHideInteractiveGoals();
    }

    /**
     * Return the number of tainted exploration nodes in a Proof
     */
    public AtomicInteger get(Proof p) {
        return taintedProofs.computeIfAbsent(p, e -> new AtomicInteger(0));
    }

    /**
     * Triggers a property change event, and the rerendering of the proof tree.
     *
     * @see #isShowInteractiveBranches()
     */
    public void setShowInteractiveBranches(boolean showInteractiveBranches) {
        GUIProofTreeModel delegateModel =
            MainWindow.getInstance().getProofTreeView().getDelegateModel();
        delegateModel.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS,
            !showInteractiveBranches);
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
     * State whether whole application (with shown second branch) or simplified with hidden branch
     * app should be used
     */
    public enum ExplorationState {
        WHOLE_APP, SIMPLIFIED_APP
    }
}
