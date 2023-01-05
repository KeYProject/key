package org.key_project.action_history;

import de.uka.ilkd.key.gui.UserAction;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

/**
 * Simple combobox to display the actions performed by the user. Selecting a particular entry
 * does not have any effect.
 *
 * @author Arne Keller
 */
public class ActionBuffer extends JComboBox<String> {
    /**
     * Displayed action labels.
     */
    private List<String> items;
    /**
     * Display user actions (last element shown first).
     */
    private List<UserAction> userActions;

    /**
     * Construct a new action buffer.
     *
     * @param userActions list of user actions to display
     */
    public ActionBuffer(List<UserAction> userActions) {
        super();
        setUserActions(userActions);
    }

    /**
     * Show the provided list of user actions.
     *
     * @param userActions user actions to show
     */
    public void setUserActions(List<UserAction> userActions) {
        this.items = new ArrayList<>();
        this.userActions = userActions;
        removeAllItems();
        for (int i = userActions.size() - 1; i >= 0; i--) {
            String name = userActions.get(i).name();
            items.add(name);
            addItem(name);
        }
    }
}
