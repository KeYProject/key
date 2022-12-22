package org.key_project.action_history;

import de.uka.ilkd.key.control.AutoModeListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.GeneralSettings;
import org.key_project.util.collection.ImmutableList;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

public final class UndoLastAction extends MainWindowAction {

    private static final IconFontProvider UNDO = new IconFontProvider(FontAwesomeSolid.UNDO);

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
        // TODO: define accelerator key (Z is already taken by GoalBackAction?)
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        extension.undoLastAction();
    }
}
