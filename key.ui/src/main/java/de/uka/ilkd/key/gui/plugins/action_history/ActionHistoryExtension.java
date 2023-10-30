/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;


/**
 * Entry point for the Action History functionality.
 *
 * @author Arne Keller
 */
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
     */
    private UndoHistoryButton undoButton = null;
    private JButton undoUptoButton = null;
    /**
     * Proofs this extension is monitoring for changes.
     */
    private final Set<Proof> registeredProofs = new HashSet<>();
    /**
     * The currently shown proof.
     */
    private Proof currentProof = null;

    private List<UserAction> getActions() {
        List<UserAction> actions = userActions.get(currentProof);
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
        int idx = allActions.indexOf(userAction);
        for (int i = allActions.size() - 1; i >= idx; i--) {
            allActions.get(i).undo();
            allActions.remove(i);
        }
    }

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
    public void selectedNodeChanged(KeYSelectionEvent e) {
        // ignored
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
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
