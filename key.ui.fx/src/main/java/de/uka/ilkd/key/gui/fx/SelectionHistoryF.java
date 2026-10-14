/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.lang.ref.WeakReference;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.beans.property.ReadOnlyBooleanWrapper;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

/**
 * menu: MP3b — JavaFX port of the Swing {@code SelectionHistory} controller
 * (key.ui/.../gui/SelectionHistory.java, consumed by the Swing {@code SelectionBackAction} /
 * {@code SelectionForwardAction} of the View menu). Traces the proof nodes selected by the
 * user and allows navigating backwards and forwards; the navigation operations and the history
 * bookkeeping are identical to the Swing original (including the {@link WeakReference}s, the
 * pruning of disposed/pruned nodes and the {@link ProofDisposedListener} cleanup of the forward
 * history).
 * <p>
 * The only difference to the Swing class: instead of Swing change listeners, the enablement of
 * the Back/Forward actions is exposed as the JavaFX properties {@link #canGoBackProperty()} and
 * {@link #canGoForwardProperty()}, recomputed on every history change (Swing recomputes it in
 * {@code SelectionHistoryChangeListener.update}, SelectionBackAction.java:66-71).
 */
public class SelectionHistoryF implements KeYSelectionListener, ProofDisposedListener {
    /**
     * Previously selected nodes by the user. These are stored as weak references to avoid
     * keeping disposed proofs alive (Swing comment, SelectionHistory.java:36-38).
     */
    private final Deque<WeakReference<Node>> selectedNodes = new ArrayDeque<>();
    /**
     * "Forward history": nodes the user navigated away from using this facility. These don't
     * have to be stored as weak references because the user cannot dispose a referenced proof
     * without navigating to it again (thereby clearing this list) — Swing
     * SelectionHistory.java:42-44.
     */
    private final Deque<Node> selectionHistoryForward = new ArrayDeque<>();

    /**
     * Listeners watching this object for changes (Swing
     * {@code de.uka.ilkd.key.gui.SelectionHistoryChangeListener}).
     */
    private final Collection<ChangeListener> listeners = new ArrayList<>();
    /**
     * The set of proofs this object is registered as a disposed listener to.
     */
    private final Set<Proof> monitoredProofs = new HashSet<>();

    /** enablement of the Back action: a valid previous selection exists. */
    private final ReadOnlyBooleanWrapper canGoBack = new ReadOnlyBooleanWrapper(this, "canGoBack");
    /** enablement of the Forward action: a valid entry exists in the forward history. */
    private final ReadOnlyBooleanWrapper canGoForward =
        new ReadOnlyBooleanWrapper(this, "canGoForward");

    private final KeYSelectionModel selectionModel;

    /**
     * Construct a new selection history and register it on the selection model (Swing:
     * {@code mediator.addKeYSelectionListener(this)}, SelectionHistory.java:60-63).
     *
     * @param selectionModel the window's selection model
     */
    public SelectionHistoryF(KeYSelectionModel selectionModel) {
        this.selectionModel = selectionModel;
        selectionModel.addKeYSelectionListener(this);
    }

    /**
     * @return whether the Back action is available (a valid previous selection exists)
     */
    public ReadOnlyBooleanProperty canGoBackProperty() {
        return canGoBack.getReadOnlyProperty();
    }

    /**
     * @return whether the Forward action is available (a valid entry exists in the forward
     *         history)
     */
    public ReadOnlyBooleanProperty canGoForwardProperty() {
        return canGoForward.getReadOnlyProperty();
    }

    /**
     * Determine which node was previously selected by the user. May return null if the user
     * hasn't selected anything previously or that proof has been closed. Port of the Swing
     * method of the same name (SelectionHistory.java:72-96), including the pruning of stale
     * references and the "navigate one node further" edge case when the stored previous node is
     * the current selection.
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
     * Show the previously selected node (Swing {@code SelectionHistory.navigateBack},
     * SelectionHistory.java:101-113).
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
            selectionModel.setSelectedNode(previous);
            fireChangeEvent();
        }
    }

    /**
     * @return the next entry of the forward history (query method, modulo fixing up stale
     *         entries), or {@code null} — Swing {@code SelectionHistory.nextNode},
     *         SelectionHistory.java:115-135.
     */
    public Node nextNode() {
        if (!selectionHistoryForward.isEmpty()) {
            Node currentSelection = selectionModel.getSelectedNode();
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
     * Undo the last {@link #navigateBack()} call (Swing
     * {@code SelectionHistory.navigateForward}, SelectionHistory.java:140-150).
     */
    public void navigateForward() {
        // navigate to the next selection stored in the history
        Node previous = nextNode();
        if (previous != null) {
            selectionHistoryForward.removeLast();
            // add to history here to ensure the forward history isn't cleared
            selectedNodes.addLast(new WeakReference<>(previous));
            selectionModel.setSelectedNode(previous);
            fireChangeEvent();
        }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
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
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null || monitoredProofs.contains(p)) {
            return;
        }
        monitoredProofs.add(p);
        p.addProofDisposedListener(this);
    }

    private void fireChangeEvent() {
        // Swing: the change listeners update the action enablement
        // (SelectionBackAction.update, SelectionBackAction.java:66-71); here the same
        // enablement is exposed as JavaFX properties.
        canGoBack.set(hasPrevious());
        canGoForward.set(hasNext());
        for (ChangeListener l : listeners) {
            l.update();
        }
    }

    /**
     * @return whether a valid previous selection exists — the side-effect-free counterpart of
     *         the Swing enablement check {@code history.previousNode() != null}
     *         (SelectionBackAction.java:66-71): walk the history from the top, skipping the
     *         current selection and stale (disposed / pruned / garbage-collected) references.
     */
    private boolean hasPrevious() {
        Node current = selectionModel.getSelectedNode();
        Iterator<WeakReference<Node>> it = selectedNodes.descendingIterator();
        while (it.hasNext()) {
            Node candidate = it.next().get();
            if (candidate == null || candidate == current) {
                continue;
            }
            if (!candidate.proof().isDisposed() && candidate.proof().find(candidate)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return whether the forward history contains a valid entry (Swing
     *         {@code SelectionForwardAction.update}: {@code history.nextNode() != null},
     *         SelectionForwardAction.java:65-70)
     */
    private boolean hasNext() {
        for (Node candidate : selectionHistoryForward) {
            if (candidate != null && !candidate.proof().isDisposed()
                    && candidate.proof().find(candidate)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Adds a change listener notified on every history change (Swing
     * {@code SelectionHistoryChangeListener}); the Back/Forward menu items use the JavaFX
     * enablement properties instead.
     *
     * @param listener the listener, not {@code null}
     */
    public void addChangeListener(ChangeListener listener) {
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

    /**
     * Listener notified whenever the history changed (the FX counterpart of the Swing
     * {@code SelectionHistoryChangeListener} interface).
     */
    @FunctionalInterface
    public interface ChangeListener {
        void update();
    }
}
