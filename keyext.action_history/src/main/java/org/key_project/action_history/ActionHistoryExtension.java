package org.key_project.action_history;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.UserAction;
import de.uka.ilkd.key.gui.UserActionListener;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.proof.Proof;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
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
    description = "GUI extension to undo actions (using a toolbar button)\nAuthor: Arne Keller <arne.keller@posteo.de>",
    experimental = false, optional = true, priority = 10000)
public class ActionHistoryExtension implements KeYGuiExtension,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, UserActionListener, KeYSelectionListener {
    /**
     * Icon for the undo button.
     */
    private static final IconFontProvider UNDO = new IconFontProvider(FontAwesomeSolid.UNDO);

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
    private DropdownSelectionButton actionBuffer = null;

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (extensionToolbar == null) {
            extensionToolbar = new JToolBar();
            actionBuffer = new DropdownSelectionButton(MainWindow.TOOLBAR_ICON_SIZE, UNDO, "Undo ",
                this::undoOneAction, this::undoUptoAction);
            JButton undoButton = actionBuffer.getActionButton();
            undoButton.setToolTipText("Undo the last action performed on the proof");
            extensionToolbar.add(undoButton);
            JButton undoUptoButton = actionBuffer.getSelectionButton();
            undoUptoButton.setToolTipText(
                "Select an action to undo, including all actions performed afterwards");
            extensionToolbar.add(undoUptoButton);
        }
        return extensionToolbar;
    }

    private void undoOneAction(UserAction userAction) {
        List<UserAction> allActions = userActions.get(userAction.getProof());
        assert !allActions.isEmpty();
        assert allActions.get(allActions.size() - 1) == userAction;
        allActions.remove(allActions.size() - 1);

        userAction.undo();

        actionBuffer.setItems(allActions);
    }

    private void undoUptoAction(UserAction userAction) {
        List<UserAction> allActions = userActions.get(userAction.getProof());
        int idx = allActions.indexOf(userAction);
        for (int i = allActions.size() - 1; i >= idx; i--) {
            allActions.get(i).undo();
            allActions.remove(i);
        }
        actionBuffer.setItems(allActions);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.addUserActionListener(this);
        mediator.addKeYSelectionListener(this);
        new StateChangeListener(mediator);
    }

    @Override
    public void actionPerformed(UserAction action) {
        List<UserAction> userActionList =
            userActions.computeIfAbsent(action.getProof(), x -> new ArrayList<>());
        userActionList.add(action);
        actionBuffer.setItems(userActionList);
    }

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        /* ignore */
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        currentProof = e.getSource().getSelectedProof();
        if (userActions.containsKey(currentProof)) {
            actionBuffer.setItems(userActions.get(currentProof));
        }
    }
}
