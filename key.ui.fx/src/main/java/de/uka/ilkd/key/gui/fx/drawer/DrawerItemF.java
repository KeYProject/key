/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.drawer;

import javafx.beans.property.BooleanProperty;
import javafx.collections.ListChangeListener;
import javafx.scene.Node;
import javafx.scene.control.TitledPane;
import javafx.scene.control.ToggleButton;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * One entry of a {@link DrawerF}: a toggle button in the drawer's button bar plus the content
 * shown in the drawer's content area while the item is expanded. Port of the TornadoFX
 * {@code DrawerItem} (Kotlin: {@code tornadofx.Drawer.kt}).
 *
 * <p>
 * The expanded state is the selected state of the underlying {@link ToggleButton}; the owning
 * drawer reacts to changes and inserts/removes this item from its content area in button order.
 * When the constructor's {@code showHeader} flag is set, a non-collapsible {@link TitledPane}
 * header (text = title) is rendered above the content to distinguish the item in multiselect
 * mode (TornadoFX parameter {@code showHeader}, default {@code true} when multiselect is
 * enabled).
 *
 * <p>
 * Items are transferable between drawers (drag and drop to another port); the owner reference is
 * updated accordingly by {@link DrawerF#transferItem(DrawerItemF, DrawerF)}.
 */
public class DrawerItemF extends VBox {

    /** The drawer currently owning this item; updated on transfer to another drawer. */
    private DrawerF drawer;

    /** Stable identity used by the drag-and-drop registry, independent of index or owner. */
    private final long itemId;

    private final ToggleButton button = new ToggleButton();

    private TitledPane header;

    private final BooleanProperty expandedProperty;

    DrawerItemF(DrawerF drawer, String title, Node graphic, boolean showHeader) {
        this.drawer = drawer;
        this.itemId = DrawerF.nextItemId();
        this.expandedProperty = button.selectedProperty();
        if (title != null) {
            button.setText(title);
        }
        if (graphic != null) {
            button.setGraphic(graphic);
        }
        getChildren().addListener((ListChangeListener<Node>) change -> {
            while (change.next()) {
                if (change.wasAdded()) {
                    for (Node added : change.getAddedSubList()) {
                        if (added != header && VBox.getVgrow(added) == null) {
                            VBox.setVgrow(added, Priority.ALWAYS);
                        }
                    }
                }
            }
        });
        if (showHeader) {
            header = new TitledPane();
            header.setText(title);
            header.setCollapsible(false);
            getChildren().add(header);
        }
        applySelectedStyle(button.isSelected());
        button.selectedProperty().addListener((obs, wasSelected, isSelected) -> {
            applySelectedStyle(isSelected);
            this.drawer.updateExpanded(this);
        });
        DrawerF.register(this);
    }

    private void applySelectedStyle(boolean selected) {
        // TornadoFX DrawerStyles.buttonArea toggleButton:selected -> #818181 background,
        // white text (DrawerStyles.kt).
        button.setStyle(selected
                ? "-fx-background-color: #818181; -fx-text-fill: white;"
                : "");
    }

    /** @return the drawer currently owning this item */
    public DrawerF getDrawer() {
        return drawer;
    }

    void setDrawer(DrawerF drawer) {
        this.drawer = drawer;
    }

    long getItemId() {
        return itemId;
    }

    /** @return the toggle button driving the expanded state of this item */
    public ToggleButton getButton() {
        return button;
    }

    /** @return the header above the content, or {@code null} when constructed without header */
    public TitledPane getHeader() {
        return header;
    }

    /** @return the expanded (selected) state property — equals {@code button.selectedProperty()} */
    public BooleanProperty getExpandedProperty() {
        return expandedProperty;
    }

    public boolean isExpanded() {
        return button.isSelected();
    }

    public void setExpanded(boolean expanded) {
        button.setSelected(expanded);
    }

    @Override
    public String toString() {
        return "DrawerItemF[" + itemId + (button.getText() == null ? "" : " " + button.getText())
            + "]";
    }
}
