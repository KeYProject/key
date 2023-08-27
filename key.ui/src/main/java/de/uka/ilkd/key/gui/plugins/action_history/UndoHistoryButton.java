/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.action_history;

import java.awt.event.*;
import java.util.*;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Supplier;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.actions.useractions.UserAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;

/**
 * A button consisting of an action component (normal button) and a selection menu (dropdown
 * button). Selecting an entry from the dropdown executes an action based on that entry,
 * pressing the normal button executes an action based on the top entry.
 *
 * <p>
 * This class is a heavily simplified version of
 * {@link de.uka.ilkd.key.gui.smt.DropdownSelectionButton}.
 * </p>
 *
 * @author Arne Keller
 */
public class UndoHistoryButton {

    /**
     * The dropdown opening button.
     */
    private JButton selectionComponent;
    /**
     * The action starting button.
     */
    private final UndoAction action;
    /**
     * The actions that can be selected.
     */
    private List<UserAction> items;
    /**
     * The menu items of the popup menu opened by the selection button.
     */
    private final List<JMenuItem> menuItems = new ArrayList<>();
    /**
     * A prefix prepended to every label displayed in the action/dropdown component.
     */
    private final String prefix;

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
     * The size of the action button and selection component's icon.
     */
    private final int iconSize;
    /**
     * The icon to use for the action button.
     */
    private final IconFontProvider actionIcon;
    /**
     * Callback notified about selected dropdown entries.
     */
    private final Consumer<UserAction> pressedSelection;
    /**
     * Callback that provides the actions to display.
     */
    private final Supplier<List<UserAction>> actionSupplier;

    /**
     * Create a new UndoHistoryButton with a given icon size used to display the selection
     * component's icon.
     *
     * @param mainWindow the main window
     * @param iconSize the size of the selection component's icon (e.g. down-arrow)
     * @param actionIcon icon for the action button
     * @param prefix the prefix to prepend to every label
     * @param pressedAction callback if the button is pressed / dropdown entry is selected
     * @param pressedSelection callback if a dropdown entry is selected
     * @param actionSupplier callback that provides the list of actions to display
     */
    public UndoHistoryButton(MainWindow mainWindow, int iconSize, IconFontProvider actionIcon,
            String prefix,
            Consumer<UserAction> pressedAction, Consumer<UserAction> pressedSelection,
            Supplier<List<UserAction>> actionSupplier) {
        this.iconSize = iconSize;
        this.actionIcon = actionIcon;
        this.prefix = prefix;
        this.pressedSelection = pressedSelection;
        this.action = new UndoAction(mainWindow, pressedAction);
        this.actionSupplier = actionSupplier;
    }

    /**
     * Enables or disables the action button (enabling is only possible if the items aren't empty).
     *
     * @param b true iff the action button should be enabled
     */
    public void setEnabled(boolean b) {
        if (items.isEmpty()) {
            b = false;
        }
        getAction().setEnabled(b);
        getSelectionButton().setEnabled(b);
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
                    setItems(actionSupplier.get());
                    if (!items.isEmpty()) {
                        if (!buttonShouldOpenMenu) {
                            /*
                             * Do nothing if the button should not open the menu. If the menu is not
                             * visible anymore after clicking the button, change the button's
                             * behaviour for the next click (no matter whether the mouse moves).
                             */
                            buttonShouldOpenMenu = !getMenu().isVisible();
                            return;
                        }
                        getMenu().show(getSelectionButton(), 0, getSelectionButton().getHeight());
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
     * (Create and) return the main action performed in this component.
     *
     * @return the action
     */
    public MainWindowAction getAction() {
        return action;
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
            menu = new JPopupMenu();
        }
        return menu;
    }

    /**
     * Set the actions that can be selected.
     *
     * @param it the selectable actions
     */
    private void setItems(List<UserAction> it) {
        items = it;
        menuItems.clear();

        // show at most 20 undo items
        int lastItem = Math.max(0, items.size() - 20);

        for (int i = items.size() - 1; i >= lastItem; i--) {
            UserAction item = it.get(i);
            JMenuItem menuItem = new JMenuItem();
            menuItem.setText(prefix + item.name());
            final UserAction selectedItem = item;
            menuItem.addActionListener(e -> this.pressedSelection.accept(selectedItem));
            menuItems.add(menuItem);
        }
        // inform the user if there are more actions remaining
        if (lastItem != 0) {
            JMenuItem remainingActions = new JMenuItem(String
                    .format("(%d earlier action%s not shown)", lastItem, lastItem > 1 ? "s" : ""));
            remainingActions.setEnabled(false);
            menuItems.add(remainingActions);
        }
        refreshSelectionItems(menuItems);
        setEnabled(!it.isEmpty());
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
        getMenu().pack();
    }

    /**
     * Update the UI state of this action.
     * If there are no actions to undo, the button is disabled.
     */
    public void refreshState() {
        setItems(actionSupplier.get());
        // ^ automatically enables / disables button
    }

    /**
     * The main purpose of this GUI component: the undo button / action.
     */
    public final class UndoAction extends MainWindowAction {

        /**
         * Calling this function should perform the undo operation.
         */
        private final Consumer<UserAction> callback;

        /**
         * Construct a new undo action.
         *
         * @param mainWindow main window
         * @param callback callback responsible for undoing actions
         */
        UndoAction(MainWindow mainWindow, Consumer<UserAction> callback) {
            super(mainWindow);
            setIcon(actionIcon.get(iconSize));
            setTooltip("Undo the last action performed on the proof");
            this.callback = callback;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            setItems(actionSupplier.get());
            if (!items.isEmpty()) {
                callback.accept(items.get(items.size() - 1));
            }
        }
    }
}
