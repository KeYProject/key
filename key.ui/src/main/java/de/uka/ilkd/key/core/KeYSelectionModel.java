/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.*;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 *
 */
@NullMarked
public class KeYSelectionModel {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYSelectionModel.class);

    // the KeYMediator is informed before all
    private final KeYMediator primary;

    protected final PropertyChangeSupport propertyChangeSupport = new PropertyChangeSupport(this);

    /**
     * the proof to listen to
     */
    private @Nullable Proof proof;
    public static String PROPERTY_SELECTED_PROOF = "proof";

    /**
     * is the selected node a goal
     */
    private @Nullable Goal selectedGoal;
    public static String PROPERTY_SELECTED_GOAL = "selectedGoal";


    /**
     * the current displayed node
     */
    private @Nullable Node selectedNode;
    public static String PROPERTY_SELECTED_NODE = "selectedNode";


    /**
     * The currently displayed sequent. Equal to the sequent of {@link #selectedNode} unless
     * we are displaying an OSS node.
     */
    private @Nullable Sequent selectedSequent;
    public static String PROPERTY_SELECTED_SEQUENT = "selectedSequent";


    /**
     * The currently displayed rule application. Equal to the rule app of {@link #selectedNode}
     * unless we are displaying an OSS node.
     */
    private @Nullable RuleApp selectedRuleApp;
    public static String PROPERTY_SELECTED_RULE_APP = "selectedRuleApp";


    /**
     * the listeners to this model
     */
    private final List<KeYSelectionListener> listenerList;

    /**
     * cached selected node event
     */

    public KeYSelectionModel(KeYMediator primary) {
        this.primary = primary;
        listenerList = Collections.synchronizedList(new ArrayList<>(5));
    }

    /// @see PropertyChangeSupport#addPropertyChangeListener(PropertyChangeListener)
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(listener);
    }

    /// @see PropertyChangeSupport#removePropertyChangeListener(PropertyChangeListener)
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(listener);
    }

    /// @see PropertyChangeSupport#getPropertyChangeListeners()
    public PropertyChangeListener[] getPropertyChangeListeners() {
        return propertyChangeSupport.getPropertyChangeListeners();
    }

    /// @see PropertyChangeSupport#addPropertyChangeListener(String, PropertyChangeListener)
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
    }

    /// @see PropertyChangeSupport#removePropertyChangeListener(String, PropertyChangeListener)
    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        propertyChangeSupport.removePropertyChangeListener(propertyName, listener);
    }

    /**
     * Sets the selected proof.
     *
     * @param p the proof to select.
     * @see KeYMediator#getSelectionModel()#setProof(Proof)
     */
    public synchronized void setSelectedProof(Proof p) {
        final Proof previousProof = proof;
        proof = p;
        primary.setProof(p, previousProof);
        if (proof != null) {
            if (proof.openGoals().isEmpty()) {
                setSelectedNode(proof.root().leavesIterator().next());
            } else {
                final Goal g = proof.openGoals().iterator().next();
                setSelectedGoal(g);
            }
        } else {
            setSelectedNode(null);
            setSelectedSequent(null);
            setSelectedRuleApp(null);
            setSelectedGoal(null);
        }

        propertyChangeSupport.firePropertyChange(PROPERTY_SELECTED_PROOF, previousProof, proof);
        fireSelectedProofChanged(previousProof);
    }

    /**
     * returns the proof that is selected by the user
     *
     * @return the proof that is selected by the user
     */
    public Proof getSelectedProof() {
        return proof;
    }

    /**
     * sets the node that is focused by the user
     *
     * @param n the selected node
     */
    public synchronized void setSelectedNode(@Nullable Node n) {
        final Node previousSelectedNode = selectedNode;
        // switch proof if needed
        if (n.proof() != getSelectedProof()) {
            setSelectedProof(n.proof());
        }
        selectedNode = n;
        setSelectedGoal(null);
        setSelectedRuleApp(selectedNode.getAppliedRuleApp());
        setSelectedSequent(selectedNode.sequent());
        fireSelectedNodeChanged(previousSelectedNode);
        propertyChangeSupport.firePropertyChange(PROPERTY_SELECTED_NODE, previousSelectedNode,
            selectedGoal);
    }

    /**
     * Sets the node and sequent focused by the user.
     *
     * @param node selected node
     * @param sequent selected sequent
     * @param ruleApp a rule app
     */
    public synchronized void setSelectedSequentAndRuleApp(
            @Nullable Node node, @Nullable Sequent sequent, @Nullable RuleApp ruleApp) {
        setSelectedNode(node);
        setSelectedSequent(sequent);
        setSelectedRuleApp(ruleApp);
    }

    /**
     * sets the node that is focused by the user
     *
     * @param g the Goal that contains the selected node
     */
    public synchronized void setSelectedGoal(@Nullable Goal g) {
        final Node previousNode = selectedNode;
        selectedGoal = g;
        setSelectedNode(g == null ? null : g.node());
        setSelectedSequent(g == null ? null : g.node().sequent());
        setSelectedRuleApp(g == null ? null : g.node().getAppliedRuleApp());
        fireSelectedNodeChanged(previousNode);
        propertyChangeSupport.firePropertyChange(PROPERTY_SELECTED_GOAL, previousNode,
            selectedGoal);
    }

    private void setSelectedRuleApp(@Nullable RuleApp ruleApp) {
        var old = selectedRuleApp;
        selectedRuleApp = ruleApp;
        propertyChangeSupport.firePropertyChange(PROPERTY_SELECTED_RULE_APP, old, ruleApp);
    }

    private void setSelectedSequent(@Nullable Sequent sequent) {
        var old = selectedSequent;
        selectedSequent = sequent;
        propertyChangeSupport.firePropertyChange(PROPERTY_SELECTED_SEQUENT, old, sequent);
    }

    /**
     * returns the node that is selected by the user
     *
     * @return the node that is selected by the user
     */
    public @Nullable Node getSelectedNode() {
        return selectedNode;
    }

    public @Nullable Sequent getSelectedSequent() {
        return selectedSequent;
    }

    public @Nullable RuleApp getSelectedRuleApp() {
        return selectedRuleApp;
    }

    /**
     * returns the goal the selected node belongs to, null if it is an inner node
     *
     * @return the goal the selected node belongs to, null if it is an inner node
     */
    public @Nullable Goal getSelectedGoal() {
        if (proof == null) {
            throw new IllegalStateException("No proof loaded.");
        }
        if (!isGoal()) {
            setSelectedGoal(proof.getOpenGoal(getSelectedNode()));
        }
        return selectedGoal;
    }

    /**
     * returns true iff the selected node is a goal
     *
     * @return true iff the selected node is a goal
     */
    public boolean isGoal() {
        return selectedGoal != null;
    }

    /**
     * enumerate the possible goal selections, starting with the best one
     */
    protected class DefaultSelectionIterator implements Iterator<Goal> {
        private static final int POS_START = 0;
        private static final int POS_LEAVES = 1;
        private static final int POS_GOAL_LIST = 2;

        private int currentPos = POS_START;
        private @Nullable Goal nextOne;
        private @Nullable Iterator<Goal> goalIt;
        private @Nullable Iterator<Node> nodeIt;

        public DefaultSelectionIterator() {
            findNext();
        }

        private void findNext() {
            nextOne = null;
            while (nextOne == null) {
                switch (currentPos) {
                    case POS_START -> {
                        currentPos = POS_LEAVES;
                        if (selectedNode != null) {
                            nodeIt = selectedNode.leavesIterator();
                        } else {
                            nodeIt = null;
                        }
                    }
                    case POS_LEAVES -> {
                        if (nodeIt == null || !nodeIt.hasNext()) {
                            currentPos = POS_GOAL_LIST;
                            if (!proof.openGoals().isEmpty()) {
                                goalIt = proof.openGoals().iterator();
                            } else {
                                goalIt = null;
                            }
                        } else {
                            nextOne = proof.getOpenGoal(nodeIt.next());
                        }
                    }
                    case POS_GOAL_LIST -> {
                        if (goalIt == null || !goalIt.hasNext()) {
                            // no more items
                            return;
                        } else {
                            nextOne = goalIt.next();
                        }
                    }
                }
            }
        }

        @Override
        public Goal next() {
            Goal res = nextOne;
            findNext();
            return res;
        }

        @Override
        public boolean hasNext() {
            return nextOne != null;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * selects the first goal in the goal list of proof if available if not it selects a leaf of the
     * proof tree
     */
    public void defaultSelection() {
        Goal g = null;
        Iterator<Goal> it = new DefaultSelectionIterator();

        while (g == null && it.hasNext()) {
            g = it.next();
        }

        /*
         * Order of preference: 1. Not yet closable goals 2. Goals which are not closed for all
         * metavariable instantiations 3. The first node of the tree
         */
        if (g != null) {
            setSelectedGoal(g);
        } else {
            setSelectedNode(proof.root().leavesIterator().next());
        }
    }

    public void addKeYSelectionListenerChecked(KeYSelectionListener listener) {
        synchronized (listenerList) {
            if (!listenerList.contains(listener)) {
                addKeYSelectionListener(listener);
            }
        }
    }

    public void addKeYSelectionListener(KeYSelectionListener listener) {
        synchronized (listenerList) {
            LOGGER.trace("Adding {}", listener.getClass());
            listenerList.add(listener);
        }
    }

    public void removeKeYSelectionListener(KeYSelectionListener listener) {
        synchronized (listenerList) {
            LOGGER.trace("Removing {}", listener.getClass());
            listenerList.remove(listener);
        }
    }

    public synchronized void fireSelectedNodeChanged(Node previousNode) {
        synchronized (listenerList) {
            final KeYSelectionEvent<Node> selectionEvent =
                new KeYSelectionEvent<>(this, previousNode);
            for (final KeYSelectionListener listener : listenerList) {
                listener.selectedNodeChanged(selectionEvent);
            }
        }
    }

    public synchronized void fireSelectedProofChanged(Proof previousProof) {
        synchronized (listenerList) {
            LOGGER.debug("Selected Proof changed, firing...");
            final KeYSelectionEvent<Proof> selectionEvent =
                new KeYSelectionEvent<>(this, previousProof);
            for (final KeYSelectionListener listener : listenerList) {
                listener.selectedProofChanged(selectionEvent);
            }
            LOGGER.trace("Selected Proof changed, done firing.");
        }
    }

}
