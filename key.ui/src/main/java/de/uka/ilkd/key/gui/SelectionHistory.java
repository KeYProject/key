package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.proof.Node;

import java.util.ArrayDeque;
import java.util.Deque;

/**
 * Traces the proof nodes selected by the user. Allows navigating forwards and backwards to
 * show previous proof nodes.
 *
 * @author Arne Keller
 */
public class SelectionHistory implements KeYSelectionListener {
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
     * Construct a new selection history.
     *
     * @param mediator mediator
     */
    public SelectionHistory(KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
    }

    /**
     * Show the previously selected node.
     */
    public void navigateBack() {
        if (!selectedNodes.isEmpty()) {
            // remove current selection
            Node currentSelection = selectedNodes.removeLast();
            // navigate to previous selection
            Node previous = selectedNodes.peekLast();
            // edge case: node may have been pruned away
            while (previous != null && !previous.proof().find(previous)) {
                selectedNodes.removeLast();
                previous = selectedNodes.peekLast();
            }
            if (previous != null) {
                selectionHistoryForward.addLast(currentSelection);
                mediator.getSelectionModel().setSelectedNode(previous);
            }
        }
    }

    /**
     * Undo the last {@link #navigateBack()} call.
     */
    public void navigateForward() {
        if (!selectionHistoryForward.isEmpty()) {
            // navigate to the next selection stored in the history
            Node previous = selectionHistoryForward.removeLast();
            // edge case: node may have been pruned away
            // edge case #2: proof may have been closed
            while (previous != null && !previous.proof().isDisposed()
                    && !previous.proof().find(previous)) {
                previous = selectionHistoryForward.removeLast();
            }
            if (previous != null) {
                // add to history here to ensure the forward history isn't cleared
                selectedNodes.addLast(previous);
                mediator.getSelectionModel().setSelectedNode(previous);
            }
        }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        if (selectedNodes.isEmpty()) {
            selectedNodes.add(e.getSource().getSelectedNode());
            return;
        }
        Node last = selectedNodes.peekLast();
        Node now = e.getSource().getSelectedNode();
        if (last != now) {
            selectedNodes.add(now);
        }
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        // handled by selectedNodeChanged
    }
}
