/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.drawer;

import javafx.geometry.Orientation;
import javafx.geometry.Side;
import javafx.scene.Node;
import javafx.scene.control.SplitPane;

/**
 * The content area of a {@link DrawerF}: a {@link SplitPane} hosting the content of every
 * currently expanded item. In multiselect mode several items can be expanded simultaneously
 * and their relative sizes are adjusted with the SplitPane dividers (reviewer request: the
 * previously fixed equal-growth VBox could not be resized); a freshly expanded item starts
 * with an equal share of the available space. The orientation follows the drawer's docking
 * side: a vertical stack for {@code LEFT}/{@code RIGHT} drawers, a horizontal row for
 * {@code TOP}/{@code BOTTOM} drawers.
 *
 * <p>
 * Deviation from the TornadoFX original ({@code ExpandedDrawerContentArea}, a VBox with equal
 * vertical growth): the content area is a real, divider-based SplitPane.
 *
 * @see DrawerF
 */
public class DrawerContentAreaF extends SplitPane {

    public DrawerContentAreaF() {
        setStyle("-fx-border-color: darkgray; -fx-border-width: 0.5;");
    }

    /**
     * Adapts the orientation to the drawer's docking side (called from
     * {@link DrawerF#configureDockingSide()}).
     *
     * @param side the docking side of the owning drawer
     */
    public void configureFor(Side side) {
        setOrientation(
            side == Side.TOP || side == Side.BOTTOM ? Orientation.HORIZONTAL
                    : Orientation.VERTICAL);
    }

    /** Inserts the item at the given position (appends for {@code index < 0}) and equalizes. */
    public void addItem(int index, Node item) {
        if (index < 0 || index >= getItems().size()) {
            getItems().add(item);
        } else {
            getItems().add(index, item);
        }
        equalize();
    }

    /** Removes the item and keeps the remaining dividers where the user placed them. */
    public void removeItem(Node item) {
        getItems().remove(item);
    }

    /** @return whether the item is currently hosted in the content area */
    public boolean containsItem(Node item) {
        return getItems().contains(item);
    }

    /** @return the number of currently expanded items */
    public int itemCount() {
        return getItems().size();
    }

    /** @return the expanded item at the given position (in button order) */
    public Node itemAt(int index) {
        return getItems().get(index);
    }

    /** @return the hosted (expanded) items — read-only view of the SplitPane items */
    public javafx.collections.ObservableList<Node> hostedItems() {
        return getItems();
    }

    /** @return whether no item is expanded */
    public boolean isEmpty() {
        return getItems().isEmpty();
    }

    /** distributes the available space equally over the hosted items */
    private void equalize() {
        int n = getItems().size();
        if (n < 2) {
            return;
        }
        double[] positions = new double[n - 1];
        for (int i = 0; i < n - 1; i++) {
            positions[i] = (i + 1) / (double) n;
        }
        setDividerPositions(positions);
    }

    /**
     * Replaces the hosted items with the given list (button order resync after a drag-and-drop
     * reorder) and distributes the space equally.
     *
     * @param expandedItems the expanded items in button order
     */
    public void resync(java.util.List<DrawerItemF> expandedItems) {
        getItems().setAll(expandedItems);
        equalize();
    }
}
