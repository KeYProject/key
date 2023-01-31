package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;

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
     */
    private final Deque<Node> selectedNodes = new ArrayDeque<>();
    /**
     * "Forward history": nodes the user navigated away from using this facility.
     */
    private final Deque<Node> selectionHistoryForward = new ArrayDeque<>();

    /**
     * Listeners watching this object for changes.
     */
    private final Collection<SelectionHistoryChangeListener> listeners = new ArrayList<>();

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
            Node currentSelection = selectedNodes.removeLast();
            // navigate to previous selection
            Node previous = selectedNodes.peekLast();
            // edge case: node may have been pruned away / proof may have been disposed
            // (this leads to another edge case: previous == currentSelection, in that
            // case we need to navigate one node further)
            while (previous != null && (previous.proof().isDisposed()
                    || !previous.proof().find(previous)
                    || previous == currentSelection)) {
                selectedNodes.removeLast();
                previous = selectedNodes.peekLast();
            }
            if (previous != null) {
                selectedNodes.addLast(previous);
            }
            selectedNodes.addLast(currentSelection);
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
            Node currentSelection = selectedNodes.removeLast();
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
                previous = selectionHistoryForward.removeLast();
            }
            // this is a query method, re-instantiate previous state
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
                selectedNodes.addLast(previous);
                mediator.getSelectionModel().setSelectedNode(previous);
                fireChangeEvent();
            }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        if (selectedNodes.isEmpty()) {
            selectedNodes.add(e.getSource().getSelectedNode());
            fireChangeEvent();
            return;
        }
        Node last = selectedNodes.peekLast();
        Node now = e.getSource().getSelectedNode();
        if (last != now) {
            selectedNodes.add(now);
            fireChangeEvent();
        }
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        // handled by selectedNodeChanged
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
        fireChangeEvent();
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        
    }
}
