/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.util.*;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class KeYSelectionModel {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYSelectionModel.class);

    /** the proof to listen to */
    private Proof proof;
    /** if true the selectedGoal field below can be trusted */
    private boolean goalIsValid;
    /** is the selected node a goal */
    private Goal selectedGoal;
    /** the current displayed node */
    private Node selectedNode;
    /**
     * The currently displayed sequent. Equal to the sequent of {@link #selectedNode} unless
     * we are displaying an OSS node.
     */
    private Sequent selectedSequent;
    /**
     * The currently displayed rule application. Equal to the rule app of {@link #selectedNode}
     * unless we are displaying an OSS node.
     */
    private RuleApp selectedRuleApp;
    /** the listeners to this model */
    private final List<KeYSelectionListener> listenerList;
    /** cached selected node event */
    private final KeYSelectionEvent selectionEvent = new KeYSelectionEvent(this);

    public KeYSelectionModel() {
        listenerList = Collections.synchronizedList(new ArrayList<>(5));
        goalIsValid = false;
    }

    /**
     * Does not take care of GUI effects
     */
    public void setProof(Proof p) {
        proof = Objects.requireNonNull(p);
        Goal g = proof.openGoals().iterator().next();
        if (g == null) {
            selectedNode = proof.root().leavesIterator().next();
            selectedSequent = selectedNode.sequent();
            selectedRuleApp = selectedNode.getAppliedRuleApp();
        } else {
            goalIsValid = true;
            selectedNode = g.node();
            selectedSequent = selectedNode.sequent();
            selectedRuleApp = selectedNode.getAppliedRuleApp();
            selectedGoal = g;
        }
    }

    /**
     * Sets the selected proof.
     *
     * @param p the proof to select.
     *
     * @see KeYMediator#setProof(Proof)
     */
    public void setSelectedProof(Proof p) {
        goalIsValid = false;
        proof = p;
        if (proof != null) {
            Goal g = proof.openGoals().iterator().next();
            if (g == null) {
                selectedNode = proof.root().leavesIterator().next();
                selectedSequent = selectedNode.sequent();
                selectedRuleApp = selectedNode.getAppliedRuleApp();
            } else {
                goalIsValid = true;
                selectedNode = g.node();
                selectedSequent = selectedNode.sequent();
                selectedRuleApp = selectedNode.getAppliedRuleApp();
                selectedGoal = g;
            }
        } else {
            selectedNode = null;
            selectedSequent = null;
            selectedRuleApp = null;
            selectedGoal = null;
        }
        fireSelectedProofChanged();
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
    public void setSelectedNode(Node n) {
        // switch proof if needed
        if (n.proof() != getSelectedProof()) {
            setSelectedProof(n.proof());
        }
        goalIsValid = false;
        selectedNode = n;
        selectedSequent = selectedNode.sequent();
        selectedRuleApp = selectedNode.getAppliedRuleApp();
        fireSelectedNodeChanged();
    }

    /**
     * Sets the node and sequent focused by the user.
     *
     * @param node selected node
     * @param sequent selected sequent
     */
    public void setSelectedSequentAndRuleApp(Node node, Sequent sequent, RuleApp ruleApp) {
        // switch proof if needed
        if (node.proof() != getSelectedProof()) {
            setSelectedProof(node.proof());
        }
        goalIsValid = true;
        selectedGoal = null;
        selectedNode = node;
        selectedSequent = sequent;
        selectedRuleApp = ruleApp;
        fireSelectedNodeChanged();
    }

    /**
     * sets the node that is focused by the user
     *
     * @param g the Goal that contains the selected node
     */
    public void setSelectedGoal(Goal g) {
        goalIsValid = true;
        selectedGoal = g;
        selectedNode = g.node();
        selectedSequent = selectedNode.sequent();
        selectedRuleApp = selectedNode.getAppliedRuleApp();
        fireSelectedNodeChanged();
    }

    /**
     * returns the node that is selected by the user
     *
     * @return the node that is selected by the user
     */
    public Node getSelectedNode() {
        return selectedNode;
    }

    public Sequent getSelectedSequent() {
        return selectedSequent;
    }

    public RuleApp getSelectedRuleApp() {
        return selectedRuleApp;
    }

    /**
     * returns the goal the selected node belongs to, null if it is an inner node
     *
     * @return the goal the selected node belongs to, null if it is an inner node
     */
    public Goal getSelectedGoal() {
        if (proof == null) {
            throw new IllegalStateException("No proof loaded.");
        }
        if (!goalIsValid) {
            selectedGoal = proof.getOpenGoal(selectedNode);
            goalIsValid = true;
        }
        return selectedGoal;
    }

    /**
     * returns true iff the selected node is a goal
     *
     * @return true iff the selected node is a goal
     */
    public boolean isGoal() {
        if (!goalIsValid) {
            return (getSelectedGoal() != null);
        }
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
        private Goal nextOne;
        private Iterator<Goal> goalIt;
        private Iterator<Node> nodeIt;

        public DefaultSelectionIterator() {
            findNext();
        }

        private void findNext() {
            nextOne = null;
            while (nextOne == null) {
                switch (currentPos) {
                case POS_START:
                    currentPos = POS_LEAVES;
                    if (selectedNode != null) {
                        nodeIt = selectedNode.leavesIterator();
                    } else {
                        nodeIt = null;
                    }
                    break;
                case POS_LEAVES:
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
                    break;

                case POS_GOAL_LIST:
                    if (goalIt == null || !goalIt.hasNext()) {
                        // no more items
                        return;
                    } else {
                        nextOne = goalIt.next();
                    }
                    break;
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
        Goal firstG = null;
        Iterator<Goal> it = new DefaultSelectionIterator();

        while (g == null && it.hasNext()) {
            g = it.next();
            if (firstG == null) {
                firstG = g;
            }
        }

        /*
         * Order of preference: 1. Not yet closable goals 2. Goals which are not closed for all
         * metavariable instantiations 3. The first node of the tree
         */
        if (g != null) {
            setSelectedGoal(g);
        } else {
            if (firstG != null) {
                setSelectedGoal(firstG);
            } else {
                setSelectedNode(proof.root().leavesIterator().next());
            }
        }
    }

    /**
     * selects the first open goal below the given node <tt>old</tt> if no open goal is available
     * node <tt>old</tt> is selected. In case that <tt>old</tt> has been removed from the proof the
     * proof root is selected
     *
     * @param old the Node to start looking for open goals
     */
    // XXX this method is never used
    public void nearestOpenGoalSelection(Node old) {
        Node n = old;
        while (n != null && n.isClosed()) {
            n = n.parent();
        }
        if (n == null) {
            if (proof.find(old)) {
                setSelectedNode(old);
            } else {
                setSelectedNode(proof.root());
            }
        } else {
            final Goal g = getFirstOpenGoalBelow(n);
            if (g == null || g.node() == null) {
                setSelectedNode(proof.root());
            } else {
                setSelectedGoal(g);
            }
        }
    }

    /**
     * retrieves the first open goal below the given node, i.e. the goal containing the first leaf
     * of the subtree starting at <code>n</code> which is not already closed
     *
     * @param n the Node where to start from
     * @return the goal containing the first leaf of the subtree starting at <code>n</code>, which
     *         is not already closed. <code>null</code> is returned if no such goal exists.
     */
    private Goal getFirstOpenGoalBelow(Node n) {
        final Iterator<Node> it = n.leavesIterator();
        while (it.hasNext()) {
            final Node node = it.next();
            if (!node.isClosed()) {
                return proof.getOpenGoal(node);
            }
        }
        return null;
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

    public synchronized void fireSelectedNodeChanged() {
        synchronized (listenerList) {
            for (final KeYSelectionListener listener : listenerList) {
                listener.selectedNodeChanged(selectionEvent);
            }
        }
    }

    public synchronized void fireSelectedProofChanged() {
        synchronized (listenerList) {
            LOGGER.debug("Selected Proof changed, firing...");
            for (final KeYSelectionListener listener : listenerList) {
                listener.selectedProofChanged(selectionEvent);
            }
            LOGGER.trace("Selected Proof changed, done firing.");
        }
    }

}
