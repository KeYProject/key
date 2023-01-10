package org.key_project.action_history;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.UserAction;
import de.uka.ilkd.key.gui.UserActionListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.proof.Proof;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;


/**
 * Entry point for the Action History extension.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Action History",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false, optional = true, priority = 10000)
public class ActionHistoryExtension implements KeYGuiExtension,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, UserActionListener, KeYSelectionListener {
    /**
     * Tracked user actions, stored separately for each proof.
     */
    private final Map<Proof, List<UserAction>> userActions = new WeakHashMap<>();
    /**
     * Currently selected proof. Used to control the undo buffer show in the toolbar.
     */
    private Proof currentProof = null;

    /**
     * The toolbar area for this extension. Contains the dropdown list of performed actions and
     * the undo button.
     */
    private JToolBar extensionToolbar = null;
    /**
     * Dropdown list of performed actions.
     */
    private ActionBuffer actionBuffer = null;

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (extensionToolbar == null) {
            extensionToolbar = new JToolBar();
            actionBuffer = new ActionBuffer(List.of());
            extensionToolbar.add(actionBuffer);
            extensionToolbar.add(new UndoLastAction(mainWindow, this));
        }
        return extensionToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addUserActionListener(this);
        mediator.addKeYSelectionListener(this);
    }

    @Override
    public void actionPerformed(UserAction action) {
        List<UserAction> userActionList = userActions.computeIfAbsent(action.getProof(), x -> new ArrayList<>());
        userActionList.add(action);
        actionBuffer.setUserActions(userActionList);
    }

    void undoLastAction() {
        List<UserAction> userActionList = userActions.get(currentProof);
        if (userActionList != null && !userActionList.isEmpty()) {
            UserAction a = userActionList.remove(userActionList.size() - 1);
            a.undo();
            actionBuffer.setUserActions(userActionList);
        }
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        /* ignore */
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        currentProof = e.getSource().getSelectedProof();
        if (userActions.containsKey(currentProof)) {
            actionBuffer.setUserActions(userActions.get(currentProof));
        }
    }
}
