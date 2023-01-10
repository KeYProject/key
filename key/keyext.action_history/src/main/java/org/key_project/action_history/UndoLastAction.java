package org.key_project.action_history;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;

import java.awt.event.ActionEvent;

/**
 * Toolbar button to undo the last performed {@link de.uka.ilkd.key.gui.UserAction}.
 *
 * @author Arne Keller
 */
public final class UndoLastAction extends MainWindowAction {

    /**
     * Icon for this button.
     */
    private static final IconFontProvider UNDO = new IconFontProvider(FontAwesomeSolid.UNDO);

    /**
     * The action history extension, used to implement the button's functionality.
     */
    private final ActionHistoryExtension extension;

    /**
     * Creates a new UndoLastAction.
     *
     * @param mainWindow main window
     * @param extension the extension this action belongs to
     */
    public UndoLastAction(MainWindow mainWindow, ActionHistoryExtension extension) {
        super(mainWindow);
        this.extension = extension;
        putValue(SMALL_ICON, UNDO.get(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Undo the last action.");
        // TODO: define accelerator key? (Z is already taken by GoalBackAction)
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        extension.undoLastAction();
    }
}
