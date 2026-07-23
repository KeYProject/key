/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class KeYSelectionModel {
    private static final Logger LOGGER = LoggerFactory.getLogger(KeYSelectionModel.class);

    // the KeYMediator is informed before all
    private final @NonNull KeYMediator primary;

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

    public KeYSelectionModel(@NonNull KeYMediator primary) {
        this.primary = primary;
        listenerList = Collections.synchronizedList(new ArrayList<>(5));
        goalIsValid = false;
    }

    /**
     * Sets the selected proof.
     *
     * @param p the proof to select.
     *
     * @see KeYMediator#getSelectionModel()#setProof(Proof)
     */
    public synchronized void setSelectedProof(Proof p) {
        final Proof previousProof = proof;
        goalIsValid = false;
        proof = p;
        primary.setProof(p, previousProof);
        if (proof != null) {
            if (proof.openGoals().isEmpty()) {
                selectedNode = proof.root().leavesIterator().next();
                selectedSequent = selectedNode.sequent();
                selectedRuleApp = selectedNode.getAppliedRuleApp();
            } else {
                final Goal g = proof.openGoals().iterator().next();
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
    public synchronized void setSelectedNode(Node n) {
        final Node previousSelectedNode = selectedNode;
        // switch proof if needed
        if (n.proof() != getSelectedProof()) {
            setSelectedProof(n.proof());
        }
        goalIsValid = false;
        selectedNode = n;
        selectedSequent = selectedNode.sequent();
        selectedRuleApp = selectedNode.getAppliedRuleApp();
        fireSelectedNodeChanged(previousSelectedNode);
    }

    /**
     * Sets the node and sequent focused by the user.
     *
     * @param node selected node
     * @param sequent selected sequent
     */
    public synchronized void setSelectedSequentAndRuleApp(Node node, Sequent sequent,
            RuleApp ruleApp) {
        final Node previousNode = selectedNode;
        // switch proof if needed
        if (node.proof() != getSelectedProof()) {
            setSelectedProof(node.proof());
        }
        goalIsValid = true;
        selectedGoal = null;
        selectedNode = node;
        selectedSequent = sequent;
        selectedRuleApp = ruleApp;
        fireSelectedNodeChanged(previousNode);
    }

    /**
     * sets the node that is focused by the user
     *
     * @param g the Goal that contains the selected node
     */
    public synchronized void setSelectedGoal(Goal g) {
        final Node previousNode = selectedNode;
        goalIsValid = true;
        selectedGoal = g;
        selectedNode = g.node();
        selectedSequent = selectedNode.sequent();
        selectedRuleApp = selectedNode.getAppliedRuleApp();
        fireSelectedNodeChanged(previousNode);
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
     * returns the goal the selected node belongs to, or null if there is no such goal (the selected
     * node is an inner node, or no proof is loaded at all)
     *
     * @return the selected goal, or null if there is none
     */
    public Goal getSelectedGoal() {
        // Consistent with getSelectedProof()/getSelectedNode() (both nullable) and with the
        // documented "null if inner node" contract: return null - rather than throwing - when no
        // proof is loaded. Callers already null-check this method; throwing here made GUI listeners
        // that fire during teardown (e.g. InfoView) crash with "No proof loaded".
        if (proof == null) {
            return null;
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
     * selects the first goal in the goal list of proof if available.
     * If not it selects a leaf of the proof tree
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
