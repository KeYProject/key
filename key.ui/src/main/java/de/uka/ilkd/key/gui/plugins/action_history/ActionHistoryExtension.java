/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.action_history;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.UserActionListener;
import de.uka.ilkd.key.gui.actions.useractions.UserAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Entry point for the Action History functionality.
 *
 * @author Arne Keller
 */
@NullMarked
public class ActionHistoryExtension implements UserActionListener,
        ProofDisposedListener, KeYSelectionListener {
    /**
     * Icon for the undo button.
     */
    private static final IconFontProvider UNDO = new IconFontProvider(FontAwesomeSolid.UNDO);

    /**
     * Tracked user actions, stored separately for each proof.
     */
    private final Map<Proof, List<UserAction>> userActions = new WeakHashMap<>();

    /**
     * The undo button contained in the main toolbar.
     *
     * <p>
     * The button is only created in
     * {@link #ActionHistoryExtension(MainWindow, KeYMediator)}, so the {@code null} initializer
     * is deliberate; every read happens after construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    private UndoHistoryButton undoButton = null;
    /**
     * The selection button of {@link #undoButton}.
     *
     * <p>
     * Assigned right after {@link #undoButton} in the constructor; the {@code null} initializer
     * is deliberate, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    private JButton undoUptoButton = null;
    /**
     * Proofs this extension is monitoring for changes.
     */
    private final Set<Proof> registeredProofs = new HashSet<>();
    /**
     * The currently shown proof.
     */
    private @Nullable Proof currentProof = null;

    private List<UserAction> getActions() {
        Proof proof = currentProof;
        if (proof == null) {
            return List.of();
        }
        List<UserAction> actions = userActions.get(proof);
        if (actions == null) {
            return List.of();
        }
        // filter out actions that can't be undone
        for (int i = 0; i < actions.size(); i++) {
            if (!actions.get(i).canUndo()) {
                actions.remove(i);
                i--;
            }
        }
        return actions;
    }

    private void undoOneAction(UserAction userAction) {
        List<UserAction> allActions = userActions.get(userAction.getProof());
        if (allActions == null) {
            // the action that is undone was always recorded before being invoked
            throw new NullPointerException("No recorded actions for the proof.");
        }
        assert !allActions.isEmpty();
        assert allActions.get(allActions.size() - 1) == userAction;
        allActions.remove(allActions.size() - 1);

        userAction.undo();
    }

    /**
     * Undo the provided user action after undoing every action performed after that one.
     *
     * @param userAction the action
     */
    private void undoUptoAction(UserAction userAction) {
        List<UserAction> allActions = userActions.get(userAction.getProof());
        if (allActions == null) {
            // the action that is undone was always recorded before being invoked
            throw new NullPointerException("No recorded actions for the proof.");
        }
        int idx = allActions.indexOf(userAction);
        for (int i = allActions.size() - 1; i >= idx; i--) {
            allActions.get(i).undo();
            allActions.remove(i);
        }
    }

    /**
     * Creates the extension and registers it with the mediator.
     *
     * <p>
     * The registration calls and the button configuration bind {@code this} while the receiver
     * is still under initialization (EISOP initialization check); the listeners only fire after
     * construction completes, and the buttons are only used through the toolbar afterwards,
     * suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:argument.type.incompatible",
        "nullness:methodref.receiver.bound.invalid" })
    public ActionHistoryExtension(MainWindow window, KeYMediator mediator) {
        mediator.addUserActionListener(this);
        mediator.addKeYSelectionListener(this);
        new StateChangeListener(mediator);
        undoButton =
            new UndoHistoryButton(window, MainWindow.TOOLBAR_ICON_SIZE, UNDO, "Undo ",
                this::undoOneAction, this::undoUptoAction, this::getActions);
        undoUptoButton = undoButton.getSelectionButton();
        undoUptoButton.setToolTipText(
            "Select an action to undo, including all actions performed afterwards");
        undoButton.refreshState();
    }

    @Override
    public void actionPerformed(UserAction action) {
        List<UserAction> userActionList =
            userActions.computeIfAbsent(action.getProof(), x -> new ArrayList<>());
        userActionList.add(action);
        currentProof = action.getProof();
        undoButton.refreshState();
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        Proof p = e.getSource();
        if (p == currentProof) {
            currentProof = null;
        }
        userActions.remove(p);
        registeredProofs.remove(p);
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {
        undoButton.refreshState();
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
        // ignored
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        Proof p = e.getSource().getSelectedProof();
        currentProof = p;
        if (p == null || registeredProofs.contains(p)) {
            return;
        }
        registeredProofs.add(p);
        p.addProofDisposedListener(this);
    }

    public JButton getUndoUptoButton() {
        return undoUptoButton;
    }

    public UndoHistoryButton getUndoButton() {
        return undoButton;
    }
}
