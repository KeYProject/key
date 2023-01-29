package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 */
public final class GoalSelectAboveAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 4574670781882014092L;

    /**
     * Creates a new GoalBackAction.
     *
     * @param mainWindow the main window this action belongs to
     * @param longName true iff long names (including the name of the rule to undo) shall be
     *        displayed (e.g. in menu items)
     */
    public GoalSelectAboveAction(MainWindow mainWindow) {
        super(mainWindow);
        setAcceleratorLetter(KeyEvent.VK_K);
        setName("Select Goal Above");
        setIcon(IconFactory.selectGoalAbove(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip(
            "Changes selected goal in the proof-tree to the next item above the current one");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        this.mainWindow.getProofTreeView().selectAbove();
    }
}
