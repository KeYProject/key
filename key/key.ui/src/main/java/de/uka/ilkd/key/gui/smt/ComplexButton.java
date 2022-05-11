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

import javax.swing.*;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

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
    private Function<Action[], Action> reduceChoice;
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
    // The size of the selection component's icon.
    private final int iconSize;
    // The components (other than the selection items) of the popup menu.
    private final List<Component> components = new ArrayList<>();

    private final Set<ChangeListener> listeners = new HashSet<ChangeListener>();

    private JPopupMenu menu;

    /**
     * Create a new ComplexButton with a given icon size used to display the selection
     * component's icon.
     *
     * @param iconSize the size of the selection component's icon (e.g. down-arrow)
     */
    public ComplexButton(int iconSize) {
        this.iconSize = iconSize;
    }

    /**
     * Enables or disables the action button (enabling is only possible if the items aren't empty).
     *
     * @param b true iff the action button should be enabled
     */
    public void setEnabled(boolean b) {
        if (items.length == 0) {
            b = false;
        }
        getActionButton().setEnabled(b);
        //getAction().setEnabled(b);
    }

    /**
     * Add a ChangeListener to this button that will be notified by #setSelectedItem().
     * A listener cannot be added more than once (nothing will change if it is already present).
     *
     * @param listener the new ChangeListener
     */
    public void addListener(ChangeListener listener) {
        listeners.add(listener);
    }

    /**
     * Remove a previously added ChangeListener from this button.
     *
     * @param listener the listener to remove
     */
    public void removeListener(ChangeListener listener) {
        listeners.remove(listener);
    }

    /* The two components of a ComplexButton: the action component starts the selected action,
    the selection component lets the user choose such an action out of the items.
     */

    /**
     * @return the selection button (opens the selection dropdown menu)
     */
    public JComponent getSelectionComponent() {
        return getSelectionButton();
    }

    /**
     * @return the action button (runs the selected action)
     */
    public JComponent getActionComponent() {
        return getActionButton();
    }

    /**
     * Set the action to be executed by the action component.
     *
     * @param action the action to be executed
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

    /**
     * @return whether the currently executed action is the empty item set by #setEmptyItem()
     */
    public boolean isEmptyItem() {
        return executedAction == emptyItem;
    }

    /**
     * @return the currently set empty item
     */
    public Action getEmptyItem() {
        return emptyItem;
    }

    /**
     * Set the information for the empty item.
     *
     * @param text the text displayed in the action button when the empty item is executed
     * @param toolTip the tooltip of the empty item
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
     *
     * @param prefix the new prefix
     */
    public void setPrefix(String prefix) {
        this.prefix = prefix;
    }

    /**
     * Update the action button so that it executes the selected executedAction.
     * If only one action can be chosen, make the executedAction the only element of selectedItems.
     */
    private void update() {
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

    /**
     * Check whether a given action is contained in the actions that can be selected via
     * the selection component.
     *
     * @param item the action to search
     * @return whether the given item can be selected
     */
    public boolean contains(Action item) {
        for (Object it : items) {
            if (it.equals(item)) {
                return true;
            }
        }
        return false;
    }


    /**
     * Set the executedAction to be the given one and update the action button.
     * Notify the ChangeListeners of this change.
     *
     * @param item the new executedAction
     */
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

    /**
     * (Create and) return the selection button used by #getSelectionComponent().
     * @return the selection button
     */
    protected JButton getSelectionButton() {
        if (selectionComponent == null) {
            selectionComponent = new JButton();
            selectionComponent.setFocusable(false);
            selectionComponent.addActionListener(e -> {
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
                });
            selectionComponent.setIcon(IconFactory.selectDecProcArrow(iconSize));
        }
        return selectionComponent;
    }

    /**
     * (Create and) return the action button used by #getActionComponent().
     * @return the action button
     */
    protected JButton getActionButton() {
        if (actionComponent == null) {
            actionComponent = new JButton();
            //actionComponent.setFont(actionComponent.getFont().deriveFont(iconSize*0.8f));
            // Enable the selection button iff the action button is enabled as well.
            actionComponent.addChangeListener(e -> {
                    getSelectionButton().setEnabled(actionComponent.isEnabled());
                });
        }
        return actionComponent;
    }

    /**
     * (Create and) return the dropdown popup menu that is opened by the selection component.
     * @return the popup menu opened by the selection button
     */
    protected JPopupMenu getMenu() {
        if (menu == null) {
            components.clear();
            menu = new JPopupMenu();
        }
        return menu;
    }

    /**
     * Set the actions that can be selected, the maximum amount of items that can be selected at the
     * same time (a positive integer) and the function used to create the action component's
     * action out of all the selected actions.
     *
     * @param it        the selectable actions
     * @param reduce   the function used to collapse multiple selected actions into one for the
     *                 action component
     * @param maxChoice the maximum amount of actions that can be selected,
     *                  this is assumed to be at least 1 (otherwise it is changed to be 1)
     */
    public void setItems(Action[] it, Function<Action[], Action> reduce, int maxChoice) {
        items = it;
        if (it == null) {
            items = new Action[0];
        }
        reduceChoice = reduce;
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

    /**
     * Set new selection items/actions while keeping all other components of the popup menu.
     *
     * @param newMenuItems the new actions that can be selected
     */
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

    /**
     * Add a component to the popup menu (below the selection items).
     * @param comp the added component
     */
    public void addComponent(Component comp) {
        getMenu().add(comp);
        components.add(comp);
        getMenu().pack();
    }

    /**
     * Remove a component (other than the selection items) from the popup menu.
     * @param comp the component to remove
     */
    public void removeComponent(Component comp) {
        components.remove(comp);
        getMenu().remove(comp);
        getMenu().pack();
    }

    /**
     * @return the first action of the items list or the empty item if items is empty.
     */
    public Action getTopItem() {
        if (items.length > 0) {
            return items[0];
        }
        return emptyItem;
    }

    /**
     * Select the first maxChoiceAmount items of the items list.
     */
    public void selectMaxNumber() {
        for (int i = 0; i < maxChoiceAmount; i++) {
            menuItems.get(i).setSelected(true);
        }
    }

    /**
     * Deselect all currently selected items.
     */
    public void deselectAll() {
        for (JMenuItem item : menuItems) {
            item.setSelected(false);
        }
    }

    /**
     * The empty action to be set if items is empty.
     */
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

        /**
         * Set the tooltip to be displayed if the empty item is the executedAction.
         * @param tip the new tooltip
         */
        public void setToolTip(String tip) {
            toolTip = tip;
        }

        /**
         * @return the tooltip to be displayed if the empty item is the executedAction
         */
        public String getToolTip() {
            return toolTip;
        }

        @Override
        public String toString() {
            return text;
        }

        @Override
        public boolean isEnabled() {
            return false;
        }

        /**
         * The EmptyAction does nothing.
         */
        @Override
        public void actionPerformed(ActionEvent arg0) {

        }

    }

    /**
     * CheckBox menu item that has an assigned action which is selected on single click and
     * performed + selected on double click.
     */
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

        /**
         * If the item is selected, add its corresponding action to the selectedItems,
         * otherwise remove it.
         * Set the executedAction to reduceChoice(selectedItems).
         * @param b true iff this item should be selected
         */
        @Override
        public void setSelected(boolean b) {
            if (b) {
                selectedItems.add(this.getAction());
            } else {
                selectedItems.remove(this.getAction());
            }
            super.setSelected(b);
            // Update the action button's selected action.
            setSelectedItem(reduceChoice.apply(getSelectedItems()));
        }

        /**
         * @return the corresponding action of this item
         */
        @Override
        public Action getAction() {
            return doubleClickAction;
        }

        /**
         * On double click, select this item AND execute the corresponding action.
         * @param e the event that is processed by this item
         */
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

    /**
     * MenuItem that has an assigned action which is selected as the executedAction
     * when clicking on the item.
     */
    public class MyJMenuItem extends JMenuItem {

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
