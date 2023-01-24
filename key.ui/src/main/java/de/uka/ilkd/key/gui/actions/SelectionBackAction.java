package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SelectionHistory;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

/**
 * Action to show the previously selected proof node.
 *
 * @author Arne Keller
 */
public class SelectionBackAction extends MainWindowAction {
    /**
     * Selection history (controller object).
     */
    private final SelectionHistory history;

    /**
     * Construct a new action. Make to sure to use the same {@link SelectionHistory} to
     * construct your {@link SelectionForwardAction}!
     *
     * @param mainWindow the main window
     * @param history selection history
     */
    public SelectionBackAction(MainWindow mainWindow, SelectionHistory history) {
        super(mainWindow);
        this.history = history;
        setName("Back");
        setIcon(IconFactory.PREVIOUS.get(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Undo last navigation operation.");
        setAcceleratorKey(KeyStroke.getKeyStroke(KeyEvent.VK_LEFT,
            java.awt.event.InputEvent.CTRL_DOWN_MASK | java.awt.event.InputEvent.ALT_DOWN_MASK));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        history.navigateBack();
    }
}
