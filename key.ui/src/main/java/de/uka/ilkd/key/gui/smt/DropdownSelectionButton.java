/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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

/**
 * A button consisting of an action component (normal button) and a selection component (dropdown
 * button).
 *
 * The selection button opens a dropdown menu that lets the user select some previously added
 * actions and combines those selected actions into a resulting one according to some reducing
 * function ({@link #reduceChoice}). The resulting action is executed when pressing the action
 * button.
 *
 * The selection button's dropdown menu can also contain other components
 * ({@link #addComponent(Component)}).
 *
 * @author Christoph Scheben (2011)
 * @author Alicia Appelhagen (2022)
 */
public class DropdownSelectionButton {

    /**
     * The dropdown opening button.
     */
    private JButton selectionComponent;
    /**
     * The action starting button.
     */
    private JButton actionComponent;
    /**
     * The actions that can be selected.
     */
    private Action[] items;
    /**
     * The function used to map some selected actions to the one that is to be executed. This is
     * only used if more than one item can be selected at the same time. If only one action can be
     * selected, the function that will be used is just the identity.
     */
    private Function<Action[], Action> reduceChoice;
    /**
     * The maximum amount of actions that can be selected at the same time.
     */
    private int maxChoiceAmount;
    /**
     * The menu items of the popup menu opened by the selection button.
     */
    private final List<JMenuItem> menuItems = new ArrayList<>();
    /**
     * The currently selected action items.
     */
    private final Set<Action> selectedItems = new HashSet<>();
    /**
     * An action that does nothing. This is selected if items is empty.
     */
    private final EmptyAction emptyItem = new EmptyAction(false);
    /**
     * The currently executed action when clicking the action button.
     */
    private Action executedAction = emptyItem;
    /**
     * A prefix prepended to every String displayed in the action component.
     */
    private String prefix = "";
    /**
     * The size of the selection component's icon.
     */
    private final int iconSize;

    /**
     * The components (other than the selection items) of the popup menu.
     */
    private final List<Component> components = new ArrayList<>();

    /**
     * The ChangeListeners that are notified when the selected item changes
     * ({@link #setSelectedItem(Action)}).
     */
    private final Set<ChangeListener> listeners = new HashSet<>();

    /**
     * The dropdown menu that opens when clicking the selection button.
     */
    private JPopupMenu menu;

    /**
     * True iff the next time the selection button's action is carried out it should open the popup
     * menu.
     */
    private boolean buttonShouldOpenMenu = true;

    /**
     * Create a new DropdownSelectionButton with a given icon size used to display the selection
     * component's icon.
     *
     * @param iconSize the size of the selection component's icon (e.g. down-arrow)
     */
    public DropdownSelectionButton(int iconSize) {
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
    }

    /**
     * Add a ChangeListener to this button that will be notified by #setSelectedItem(). A listener
     * cannot be added more than once (nothing will change if it is already present).
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
        return selectedItems.toArray(new Action[0]);
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
     * Update the action button so that it executes the selected executedAction. If only one action
     * can be chosen, make the executedAction the only element of selectedItems.
     */
    private void update() {
        setAction(executedAction);
        if (getAction() != null) {
            getAction().putValue(Action.NAME,
                isEmptyItem() ? executedAction.toString() : prefix + executedAction.toString());
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
     * Check whether a given action is contained in the actions that can be selected via the
     * selection component.
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
     * Set the executedAction to be the given one and update the action button. Notify the
     * ChangeListeners of this change.
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
     *
     * @return the selection button
     */
    protected JButton getSelectionButton() {
        if (selectionComponent == null) {
            selectionComponent = new JButton();
            /*
             * If the mouse is on the button and the button gets pressed (mouse is clicked), the
             * popup menu will close. The button action will only be carried out afterwards, thus
             * opening the popup menu up again - avoid that using the listener and flag: If the
             * mouse enters the button while the menu is visible, clicking the button should not
             * invoke the opening action.
             */
            selectionComponent.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseEntered(MouseEvent e) {
                    buttonShouldOpenMenu = !getMenu().isVisible();
                }

                @Override
                public void mouseExited(MouseEvent e) {
                    buttonShouldOpenMenu = true;
                }
            });
            selectionComponent.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    if (items.length > 0) {
                        if (!buttonShouldOpenMenu) {
                            /*
                             * Do nothing if the button should not open the menu. If the menu is not
                             * visible anymore after clicking the button, change the button's
                             * behaviour for the next click (no matter whether the mouse moves).
                             */
                            buttonShouldOpenMenu = !getMenu().isVisible();
                            return;
                        }
                        OptionalInt width = Arrays.stream(getMenu().getComponents())
                                .mapToInt(c -> c.getPreferredSize().width).max();
                        if (width.isEmpty()) {
                            width = OptionalInt.of(0);
                        }
                        int newWidth = Math.max(width.getAsInt(),
                            actionComponent.getWidth() + selectionComponent.getWidth());
                        getMenu().setPopupSize(newWidth, Arrays.stream(getMenu().getComponents())
                                .mapToInt(c -> c.getPreferredSize().height).sum());
                        getMenu().show(getActionButton(), 0, getActionButton().getHeight());
                        // If the menu is open and the mouse does not leave the button,
                        // make sure the button still does not reopen the menu after the next click.
                        buttonShouldOpenMenu = false;
                    }
                }
            });
            selectionComponent.setFocusable(false);
            selectionComponent.setIcon(IconFactory.selectDecProcArrow(iconSize));
        }
        return selectionComponent;
    }

    /**
     * (Create and) return the action button used by #getActionComponent().
     *
     * @return the action button
     */
    protected JButton getActionButton() {
        if (actionComponent == null) {
            actionComponent = new JButton();
            // actionComponent.setFont(actionComponent.getFont().deriveFont(iconSize*0.8f));
            // Enable the selection button iff the action button is enabled as well.
            actionComponent.addChangeListener(
                e -> getSelectionButton().setEnabled(actionComponent.isEnabled()));
            actionComponent.setFocusPainted(false);
        }
        return actionComponent;
    }

    /**
     * (Create and) return the dropdown popup menu that is opened by the selection component.
     * Deletes all added components when the menu is null, thus leading a completely fresh and empty
     * menu.
     *
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
     * same time (a positive integer) and the function used to create the action component's action
     * out of all the selected actions.
     *
     * @param it the selectable actions
     * @param reduce the function used to collapse multiple selected actions into one for the action
     *        component
     * @param maxChoice the maximum amount of actions that can be selected, this is assumed to be at
     *        least 1 (otherwise it is changed to be 1)
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
            JMenuItem menuItem = maxChoiceAmount > 1 ? new DoubleClickCheckBoxMenuItem(item)
                    : new SelectionMenuItem(item);
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
        /*
         * The menu could also be reused (just clear all its components first), but that leads to
         * weird behaviour when going from menu items with checkboxes to normal menu items [see
         * #setItems(...)]: The space where the checkbox would be if the menu item had one is also
         * free for checkbox-less menu items (rather than that empty space on the left, one would
         * just expect the text to be completely on the left).
         */
        menu = null;
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
     *
     * @param comp the added component
     */
    public void addComponent(Component comp) {
        getMenu().add(comp);
        components.add(comp);
        getMenu().pack();
    }

    /**
     * Remove a component (other than the selection items) from the popup menu.
     *
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
     * The empty action to be set if items is empty. This action does nothing and is either always
     * disabled or always enabled which causes the action component to be disabled/enabled when
     * selecting such an EmptyAction via {@link #setSelectedItem(Action)}.
     */
    public static class EmptyAction extends AbstractAction {

        private static final long serialVersionUID = 1L;

        /**
         * The text that will be displayed in a DropdownSelectionButton's action component when its
         * {@link #emptyItem} is selected.
         */
        private String text;

        /**
         * The tooltip text that will be displayed in a DropdownSelectionButton's action component
         * when its {@link #emptyItem} is selected.
         */
        private String toolTip;

        /**
         * True iff action and selection button of the DropdownSelectionButton should stay enabled
         * when calling {@link #setSelectedItem(Action)} with this EmptyAction as the parameter.
         */
        private final boolean leaveButtonsEnabled;

        /**
         * Create a new EmptyAction with text "empty".
         *
         * @param enabled the EmptyAction's {@link #leaveButtonsEnabled} attribute
         */
        public EmptyAction(boolean enabled) {
            leaveButtonsEnabled = enabled;
            setText("empty");
        }

        /**
         * Set this EmptyAction's {@link #text}.
         *
         * @param t the new text
         */
        public void setText(String t) {
            text = t;
            putValue(Action.NAME, text);
            putValue(Action.SHORT_DESCRIPTION, toolTip);
        }

        /**
         * Set this EmptyAction's {@link #toolTip}.
         *
         * @param tip the new tooltip
         */
        public void setToolTip(String tip) {
            toolTip = tip;
        }

        /**
         * @return this EmptyItem's {@link #toolTip}
         */
        public String getToolTip() {
            return toolTip;
        }

        /**
         * @return this EmptyItem's {@link #text}
         */
        @Override
        public String toString() {
            return text;
        }

        @Override
        public boolean isEnabled() {
            return leaveButtonsEnabled;
        }

        @Override
        public void actionPerformed(ActionEvent arg0) {
            /**
             * The EmptyAction does nothing.
             */
        }

    }

    /**
     * CheckBox menu item that has an assigned action which is selected on single click and
     * performed + selected on double click.
     *
     * The DropdownSelectionButton's {@link #selectedItems} are updated accordingly.
     */
    private final class DoubleClickCheckBoxMenuItem extends JCheckBoxMenuItem {

        /**
         * The associated action, this is performed when double-clicking the menu item and selected
         * when single-clicking it.
         */
        private final transient Action doubleClickAction;

        /**
         * Create a new DoubleClickCheckBoxMenuItem.
         *
         * @param action the {@link #doubleClickAction} of this menu item
         */
        private DoubleClickCheckBoxMenuItem(Action action) {
            super();
            DoubleClickCheckBoxMenuItem menuItem = this;
            super.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    /*
                     * The selection status will be changed after a click before the action is
                     * performed, so at this point, if the item was not selected before, it is now.
                     * Hence, there may be too many selected items.
                     */
                    if (getSelectedItems().length > maxChoiceAmount) {
                        /*
                         * If the selection cannot happen, set the selection status to false again
                         * and change nothing else.
                         */
                        menuItem.setSelected(false);
                    } else {
                        // Call this to invoke the update stuff in the overridden #setSelected()
                        menuItem.setSelected(menuItem.isSelected());
                    }
                }
            });
            // tooltip of the menu item:
            setToolTipText("On double-click: " + action.getValue(Action.SHORT_DESCRIPTION));
            doubleClickAction = action;
        }

        /**
         * If the item is selected, add its corresponding action to the selectedItems, otherwise
         * remove it. Set the executedAction to reduceChoice(selectedItems).
         *
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
         * On double-click, select this item AND execute the corresponding action.
         *
         * @param e the event that is processed by this item
         */
        @Override
        protected void processMouseEvent(MouseEvent e) {
            if (e.getClickCount() >= 2) {
                doubleClickAction
                        .actionPerformed(new ActionEvent(e, MouseEvent.MOUSE_CLICKED, null));
                setSelected(true);
                return;
            }
            super.processMouseEvent(e);
        }


    }

    /**
     * MenuItem that has an assigned action which is selected as the executedAction when clicking on
     * the item.
     *
     * Updates the DropdownSelectionButton's {@link #executedAction} accordingly via
     * {@link #setSelectedItem(Action)}.
     */
    private final class SelectionMenuItem extends JMenuItem {

        /**
         * The action that is selected when clicking on this menu item.
         */
        private final transient Action action;

        /**
         * Create a new SelectionMenuItem.
         *
         * @param item the menu item's {@link #action}.
         */
        public SelectionMenuItem(Action item) {
            super();
            /*
             * If an action is performed on the menu item, the only thing that should happen is
             * setting the currently selected action to this one
             */
            super.setAction(new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    setSelectedItem(item);
                }
            });
            /*
             * This has to come after the super#setAction call because that will call getAction()
             * and assume getAction() to change its return value after setting the action. Otherwise
             * that will lead to a stack overflow.
             */
            this.action = item;
        }

        /**
         * The returned action is NOT executed when clicking on this menu item. The actually
         * executed action is the one returned by {@link super#getAction()}.
         *
         * @return the item's associated {@link #action}
         */
        @Override
        public Action getAction() {
            /*
             * If the item's action is accessed, it will return the action it represents instead of
             * the one that is executed when an action is performed on the item.
             */
            return action;
        }
    }
}
