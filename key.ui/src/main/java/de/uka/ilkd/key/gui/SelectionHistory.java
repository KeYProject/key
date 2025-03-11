/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.lang.ref.WeakReference;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

/**
 * Traces the proof nodes selected by the user. Allows navigating forwards and backwards to
 * show previous proof nodes.
 *
 * @author Arne Keller
 */
public class SelectionHistory implements KeYSelectionListener, ProofDisposedListener {
    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;
    /**
     * Previously selected nodes by the user.
     * These are stored as weak references to avoid keeping disposed proofs alive.
     */
    private final Deque<WeakReference<Node>> selectedNodes = new ArrayDeque<>();
    /**
     * "Forward history": nodes the user navigated away from using this facility.
     * These don't have to be stored as weak references because the user cannot dispose a
     * referenced proof without navigating to it again (thereby clearing this list).
     */
    private final Deque<Node> selectionHistoryForward = new ArrayDeque<>();

    /**
     * Listeners watching this object for changes.
     */
    private final Collection<SelectionHistoryChangeListener> listeners = new ArrayList<>();
    /**
     * The set of proofs this object is registered as a disposed listener to.
     */
    private final Set<Proof> monitoredProofs = new HashSet<>();

    /**
     * Construct a new selection history.
     *
     * @param mediator mediator
     */
    public SelectionHistory(KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
    }

    /**
     * Determine which node was previously selected by the user.
     * May return null if the user hasn't selected anything previously or
     * that proof has been closed.
     *
     * @return a node
     */
    public Node previousNode() {
        if (!selectedNodes.isEmpty()) {
            // remove current selection
            Node currentSelection = selectedNodes.removeLast().get();
            // navigate to previous selection
            WeakReference<Node> previousNode = selectedNodes.peekLast();
            Node previous = previousNode != null ? previousNode.get() : null;
            // edge case: node may have been pruned away / proof may have been disposed
            // (this leads to another edge case: previous == currentSelection, in that
            // case we need to navigate one node further)
            while (!selectedNodes.isEmpty() && (previous == null || (previous.proof().isDisposed()
                    || !previous.proof().find(previous)
                    || previous == currentSelection))) {
                selectedNodes.removeLast();
                previousNode = selectedNodes.peekLast();
                previous = previousNode != null ? previousNode.get() : null;
            }
            if (previous != null) {
                selectedNodes.addLast(new WeakReference<>(previous));
            }
            selectedNodes.addLast(new WeakReference<>(currentSelection));
            return previous;
        }
        return null;
    }

    /**
     * Show the previously selected node.
     */
    public void navigateBack() {
        // navigate to previous selection
        Node previous = previousNode();
        if (previous != null) {
            // store current selection for "forward history"
            WeakReference<Node> currentSelectionNode = selectedNodes.removeLast();
            Node currentSelection =
                currentSelectionNode != null ? currentSelectionNode.get() : null;
            selectionHistoryForward.addLast(currentSelection);
            mediator.getSelectionModel().setSelectedNode(previous);
            fireChangeEvent();
        }
    }

    public Node nextNode() {
        if (!selectionHistoryForward.isEmpty()) {
            Node currentSelection = mediator.getSelectionModel().getSelectedNode();
            // navigate to the next selection stored in the history
            Node previous = selectionHistoryForward.removeLast();
            // edge case: node may have been pruned away
            // edge case #2: proof may have been closed
            while (previous != null && (previous.proof().isDisposed()
                    || !previous.proof().find(previous)
                    || previous == currentSelection)) {
                previous = !selectionHistoryForward.isEmpty() ? selectionHistoryForward.removeLast()
                        : null;
            }
            // this is a query method (modulo fixing up the history), re-instantiate previous state
            if (previous != null) {
                selectionHistoryForward.addLast(previous);
            }
            return previous;
        }
        return null;
    }

    /**
     * Undo the last {@link #navigateBack()} call.
     */
    public void navigateForward() {
        // navigate to the next selection stored in the history
        Node previous = nextNode();
        if (previous != null) {
            selectionHistoryForward.removeLast();
            // add to history here to ensure the forward history isn't cleared
            selectedNodes.addLast(new WeakReference<>(previous));
            mediator.getSelectionModel().setSelectedNode(previous);
            fireChangeEvent();
        }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        if (selectedNodes.isEmpty()) {
            selectedNodes.add(new WeakReference<>(e.getSource().getSelectedNode()));
            fireChangeEvent();
            return;
        }
        Node last = selectedNodes.peekLast().get();
        Node now = e.getSource().getSelectedNode();
        if (last != now) {
            selectedNodes.add(new WeakReference<>(now));
            fireChangeEvent();
        }
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null || monitoredProofs.contains(p)) {
            return;
        }
        monitoredProofs.add(p);
        p.addProofDisposedListener(this);
    }

    private void fireChangeEvent() {
        for (SelectionHistoryChangeListener l : listeners) {
            l.update();
        }
    }

    public void addChangeListener(SelectionHistoryChangeListener listener) {
        listeners.add(listener);
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        monitoredProofs.remove(e.getSource());
        // clean up forward history
        selectionHistoryForward.removeIf(x -> x.proof().isDisposed());
        fireChangeEvent();
    }
}
