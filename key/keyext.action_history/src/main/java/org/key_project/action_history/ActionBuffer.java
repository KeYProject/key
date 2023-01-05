package org.key_project.action_history;

import de.uka.ilkd.key.gui.UserAction;

import javax.swing.*;
import java.util.ArrayList;
import java.util.List;

public class ActionBuffer extends JComboBox<String> {
    private List<String> items;
    private List<UserAction> userActions;

    public ActionBuffer(List<UserAction> userActions) {
        setUserActions(userActions);
    }

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
