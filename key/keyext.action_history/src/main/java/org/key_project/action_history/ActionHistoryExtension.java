package org.key_project.action_history;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.UserAction;
import de.uka.ilkd.key.gui.UserActionListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.util.ArrayList;
import java.util.List;


/**
 * Entry point for the Action History extension.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Action History",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false, optional = true, priority = 10000)
public class ActionHistoryExtension implements KeYGuiExtension,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, UserActionListener {
    private final List<UserAction> userActions = new ArrayList<>();

    private JToolBar extensionToolbar = null;
    private ActionBuffer actionBuffer = null;

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (extensionToolbar == null) {
            extensionToolbar = new JToolBar();
            actionBuffer = new ActionBuffer(userActions);
            extensionToolbar.add(actionBuffer);
            extensionToolbar.add(new UndoLastAction(mainWindow, this));
        }
        return extensionToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addUserActionListener(this);
    }

    @Override
    public void actionPerformed(UserAction action) {
        userActions.add(action);
        actionBuffer.setUserActions(userActions);
    }

    void undoLastAction() {
        if (!userActions.isEmpty()) {
            UserAction a = userActions.remove(userActions.size() - 1);
            a.undo();
            actionBuffer.setUserActions(userActions);
        }
    }
}
