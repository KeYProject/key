// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.smt;


import java.awt.*;
import java.awt.event.*;
import java.util.*;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import ch.qos.logback.core.Layout;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

public class ComplexButton {

    // The dropdown opening button.
    private JButton selectionComponent;
    // The action starting button.
    private JButton actionComponent;
    // The actions that can be selected.
    private Action[] items;
    /* The function used to map some selected actions to the one that is to be executed.
    This is only used if more than one item can be selected at the same time.
    If only one action can be selected, the function that will be used is just the identity. */
    private Function<Action[], Action> flattenChoice;
    // The maximum amount of actions that can be selected at the same time.
    private int maxChoiceAmount;
    // The menu items of the popup menu opened by the selection button.
    private final List<JMenuItem> menuItems = new ArrayList<>();
    // The currently selected action items.
    private final Set<Action> selectedItems = new HashSet<>();
    // An action that does nothing. This is selected if items is empty.
    private final EmptyAction emptyItem = new EmptyAction();
    // The currently executed action when clicking the action button.
    private Action executedAction = emptyItem;
    // A prefix prepended to every String displayed in the action component.
    private String prefix = "";
    private final int iconSize;
    private final Collection<ChangeListener> listeners = new LinkedList<ChangeListener>();

    private JPopupMenu menu;

    /**
     * Create a new ComplexButton with a given icon size used to display the selection
     * component's icon.
     *
     * @param iconSize
     */
    public ComplexButton(int iconSize) {
        this.iconSize = iconSize;
    }

    public void setEnabled(boolean b) {
        if (items.length == 0) {
            b = false;
        }
        getActionButton().setEnabled(b);
        //getAction().setEnabled(b);
    }

    public void addListener(ChangeListener listener) {
        listeners.add(listener);
    }

    public void removeListener(ChangeListener listener) {
        listeners.remove(listener);
    }

    /* The two components of a ComplexButton: the action component starts the selected action,
    the selection component lets the user choose such an action out of the items.
     */

    public JComponent getSelectionComponent() {
        return getSelectionButton();
    }

    public JComponent getActionComponent() {
        return getActionButton();
    }

    /**
     * Set the action to be executed by the action component.
     */
    public void setAction(Action action) {
        getActionButton().setAction(action);
    }

    /**
     * @return the action that is executed by the action component
     */
    public Action getAction() {
        return getActionButton().getAction();
    }

    /**
     * @return the currently selected actions in the selection component
     */
    public Action[] getSelectedItems() {
        return selectedItems.toArray(new Action[selectedItems.size()]);
    }

    public boolean isEmptyItem() {
        return executedAction == emptyItem;
    }

    public Action getEmptyItem() {
        return emptyItem;
    }

    /**
     * Set the information for the empty item.
     */
    public void setEmptyItem(String text, String toolTip) {
        boolean update = isEmptyItem();
        emptyItem.setText(text);
        emptyItem.setToolTip(toolTip);
        if (update) {
            executedAction = emptyItem;
            update();
        }
    }

    /**
     * Set the prefix String that will be prepended to all items in the menu.
     */
    public void setPrefix(String s) {
        prefix = s;
    }

    void update() {
        setAction(executedAction);
        if (getAction() != null) {
            getAction().putValue(Action.NAME, isEmptyItem() ? executedAction.toString()
                    : prefix + executedAction.toString());
            if (isEmptyItem()) {
                getAction().putValue(Action.SHORT_DESCRIPTION, emptyItem.getToolTip());
            }
        }
        if (maxChoiceAmount == 1) {
            selectedItems.clear();
            selectedItems.add(executedAction);
        }
    }

    public boolean contains(Action item) {
        for (Object it : items) {
            if (it.equals(item)) {
                return true;
            }
        }
        return false;
    }


    public void setSelectedItem(Action item) {
        if (item == null) {
            return;
        }
        executedAction = item;
        update();
        for (ChangeListener l : listeners) {
            l.stateChanged(new ChangeEvent(this));
        }
    }

    JButton getSelectionButton() {
        if (selectionComponent == null) {
            selectionComponent = new JButton();
            selectionComponent.setFocusable(false);
            selectionComponent.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if (items.length == 0) {
                        return;
                    } else {
                        OptionalInt width = Arrays.stream(getMenu().getComponents())
                                .mapToInt(c -> c.getPreferredSize().width).max();
                        if (width.isEmpty()) {
                            width = OptionalInt.of(0);
                        }
                        getMenu().setPopupSize(
                                width.getAsInt(),
                                Arrays.stream(getMenu().getComponents())
                                        .mapToInt(c -> c.getPreferredSize().height).sum());
                        getMenu().show(getActionButton(), 0, getActionButton().getHeight());
                    }
                }
            });
            selectionComponent.setIcon(IconFactory.selectDecProcArrow(iconSize));
        }
        return selectionComponent;
    }

    JButton getActionButton() {
        if (actionComponent == null) {
            actionComponent = new JButton();
            //actionComponent.setFont(actionComponent.getFont().deriveFont(iconSize*0.8f));
            actionComponent.addChangeListener(new ChangeListener() {

                public void stateChanged(ChangeEvent arg0) {
                    getSelectionButton().setEnabled(actionComponent.isEnabled());
                }
            });
        }
        return actionComponent;
    }

    protected JPopupMenu getMenu() {
        if (menu == null) {
            menu = createNewMenu();
        }
        return menu;
    }

    protected JPopupMenu createNewMenu() {
        components.clear();
        menu = new JPopupMenu();
        return menu;
    }

    /**
     * Set the actions that can be selected, the maximum amount of items that can be selected at the
     * same time (a positive integer) and the function used to create the action component's
     * action out of all the selected actions.
     *
     * @param it        the selectable actions
     * @param flatten   the function used to collapse multiple selected actions into one for the
     *                  action component
     * @param maxChoice the maximum amount of actions that can be selected,
     *                  this is assumed to be at least 1 (otherwise it is changed to be 1)
     */
    public void setItems(Action[] it, Function<Action[], Action> flatten, int maxChoice) {
        items = it;
        if (it == null) {
            items = new Action[0];
        }
        flattenChoice = flatten;
        // make maxChoiceAmount at least 1
        maxChoiceAmount = Math.max(1, maxChoice);
        if (items.length <= 1) {
            maxChoiceAmount = 1;
        }
        Set<Action> oldSelectedItems = new HashSet<>(selectedItems);
        selectedItems.clear();
        menuItems.clear();
        for (Action item : items) {
            JMenuItem menuItem = maxChoiceAmount > 1
                    ? new MyJCheckBoxMenuItem(item) : new MyJMenuItem(item);
            if (oldSelectedItems.contains(item) && maxChoiceAmount > 1) {
                menuItem.setSelected(true);
            }
            menuItem.setEnabled(true);
            menuItem.setText(item.toString());
            menuItem.putClientProperty("CheckBoxMenuItem.doNotCloseOnMouseClick", Boolean.TRUE);
            menuItems.add(menuItem);
        }
        refreshSelectionItems(menuItems);
        if (items.length == 0) {
            setSelectedItem(emptyItem);
            setEnabled(false);
            return;
        }
        if (maxChoiceAmount <= 1) {
            setSelectedItem(contains(getAction()) ? getAction() : getTopItem());
            return;
        }
        if (getSelectedItems().length == 0) {
            menuItems.get(0).setSelected(true);
        }
    }

    public void refreshSelectionItems(Collection<JMenuItem> newMenuItems) {
        for (Component comp : getMenu().getComponents()) {
            getMenu().remove(comp);
        }
        for (JMenuItem item : newMenuItems) {
            getMenu().add(item);
        }
        for (Component comp : components) {
            getMenu().add(comp);
        }
        getMenu().pack();
    }

    private final List<Component> components = new ArrayList<>();

    public void addComponent(Component comp) {
        getMenu().add(comp);
        components.add(comp);
        getMenu().pack();
    }

    public Action getTopItem() {
        if (items.length > 0) {
            return items[0];
        }
        return emptyItem;
    }

    public void selectMaxNumber() {
        for (int i = 0; i < maxChoiceAmount; i++) {
            menuItems.get(i).setSelected(true);
        }
    }

    public void deselectAll() {
        for (JMenuItem item : menuItems) {
            item.setSelected(false);
        }
    }

    public void removeComponent(Component comp) {
        components.remove(comp);
        getMenu().remove(comp);
        getMenu().pack();
    }


    public class EmptyAction extends AbstractAction {

        private static final long serialVersionUID = 1L;
        private String text;
        private String toolTip;

        public EmptyAction() {
            setText("empty");
        }

        public void setText(String t) {
            text = t;
            putValue(Action.NAME, text);
            putValue(Action.SHORT_DESCRIPTION, toolTip);
        }

        public void setToolTip(String t) {
            toolTip = t;
        }

        public String getToolTip() {
            return toolTip;
        }

        public String toString() {
            return text;
        }

        @Override
        public boolean isEnabled() {
            return false;
        }

        public void actionPerformed(ActionEvent arg0) {

        }

    }

    // CheckBox menu item that has an assigned action which is selected on single click and
    // performed + selected on double click.
    public class MyJCheckBoxMenuItem extends JCheckBoxMenuItem {

        /* The associated action, this is performed when double-clicking the menu item
        and selected when single-clicking it. */
        private final Action doubleClickAction;

        public MyJCheckBoxMenuItem(Action action) {
            super();
            MyJCheckBoxMenuItem menuItem = this;
            super.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    /* The selection status will be changed after a click before the action
                    is performed, so at this point, if the item was not selected before, it is now.
                    Hence, there may be too many selected items.
                     */
                    if (getSelectedItems().length > maxChoiceAmount) {
                        /* If the selection cannot happen, set the selection status to false again
                        and change nothing else. */
                        menuItem.setSelected(false);
                    } else {
                        // Call this to invoke the update stuff in the overridden #setSelected()
                        menuItem.setSelected(menuItem.isSelected());
                    }
                }
            });
            // tooltip of the menu item:
            setToolTipText("On double click: " + action.getValue(Action.SHORT_DESCRIPTION));
            doubleClickAction = action;
        }

        @Override
        public void setSelected(boolean b) {
            if (b) {
                selectedItems.add(this.getAction());
            } else {
                selectedItems.remove(this.getAction());
            }
            super.setSelected(b);
            // Update the action button's selected action.
            setSelectedItem(flattenChoice.apply(getSelectedItems()));
        }

        @Override
        public Action getAction() {
            return doubleClickAction;
        }

        @Override
        protected void processMouseEvent(MouseEvent e) {
            if (e.getClickCount() >= 2) {
                doubleClickAction.actionPerformed(
                        new ActionEvent(e, MouseEvent.MOUSE_CLICKED, null));
                setSelected(true);
                return;
            }
            super.processMouseEvent(e);
        }


    }

    private class MyJMenuItem extends JMenuItem {

        private final Action action;

        public MyJMenuItem(Action item) {
            super();
            /* If an action is performed on the menu item, the only thing that should happen
            is setting the currently selected action to this one */
            super.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    setSelectedItem(item);
                }
            });
            /* This has to come after the super#setAction call because that will call getAction()
            and assume getAction() to change its return value after setting the action.
            Otherwise that will lead to a stack overflow. */
            this.action = item;
        }

        @Override
        public Action getAction() {
            /* If the item's action is accessed, it will return the action it represents instead
            of the one that is executed when an action is performed on the item. */
            return action;
        }
    }
}
