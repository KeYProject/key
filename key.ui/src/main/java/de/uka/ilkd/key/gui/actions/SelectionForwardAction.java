/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.SelectionHistory;
import de.uka.ilkd.key.gui.SelectionHistoryChangeListener;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Action to navigate forward in proof node selection history.
 *
 * @author Arne Keller
 */
public class SelectionForwardAction extends MainWindowAction
        implements SelectionHistoryChangeListener {
    /**
     * Selection history (controller object).
     */
    private final SelectionHistory history;

    /**
     * Construct a new action. Make to sure to use the same {@link SelectionHistory} to
     * construct your {@link SelectionBackAction}!
     *
     * @param mainWindow the main window
     * @param history selection history
     */
    public SelectionForwardAction(MainWindow mainWindow, SelectionHistory history) {
        super(mainWindow);
        this.history = history;
        setName("Forward");
        setIcon(IconFactory.NEXT.get(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Redo last undone navigation operation.");
    }

    /**
     * Update the state of this action after the history has been modified.
     * May enable or disable the action.
     */
    @Override
    public void update() {
        setEnabled(history.nextNode() != null);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        history.navigateForward();
    }
}
