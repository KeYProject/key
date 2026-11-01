/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;
import java.util.function.Function;

import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.input.MouseButton;
import javafx.scene.layout.StackPane;

/**
 * A tab pane that hosts one tab per {@link Dockable}, keeping tab label, graphic, content and
 * closability in sync with the dockable's properties.
 * <p>
 * Replaces the Docking Frames {@code DockTabbedPane} of the Swing module {@code key.ui}. The
 * visibility (which dockables are open in which role) is owned by the {@link DockWorkspace}; a
 * panel simply mirrors its part of that model.
 */
public class DockTabPane extends TabPane {

    private final Map<String, Tab> tabByDockableId = new HashMap<>();
    private Consumer<Dockable> onDockableClosed = dockable -> {
    };

    /**
     * Invoked when the user double-clicks a tab (Swing bibliothek: the default {@code
     * LocationModeManager.DOUBLE_CLICK_STRATEGY} switches the double-clicked dockable between
     * {@code ExtendedMode.NORMALIZED} and {@code ExtendedMode.MAXIMIZED}).
     */
    private Consumer<Dockable> onMaximizeRequested = dockable -> {
    };

    /**
     * Builds the context menu shown on a right-click into a tab (Swing bibliothek: the title
     * popup menu with the close/maximize/externalize actions plus the dockable's title actions).
     */
    private Function<Dockable, ContextMenu> contextMenuFactory = dockable -> null;

    public DockTabPane() {
        getStyleClass().add("key-dock-tab-pane");
        setTabDragPolicy(TabDragPolicy.REORDER);
        // Swing bibliothek: a double click on the dockable (title or content — the
        // DoubleClickController listens on the whole dockable) switches between the normalized
        // and the maximized mode (LocationModeManager.DOUBLE_CLICK_STRATEGY)
        setOnMouseClicked(event -> {
            if (event.getClickCount() == 2 && event.getButton() == MouseButton.PRIMARY) {
                Tab selected = getSelectionModel().getSelectedItem();
                if (selected instanceof DockTab dockTab) {
                    onMaximizeRequested.accept(dockTab.dockable);
                }
            }
        });
        // Swing bibliothek: a right click on the title opens the action popup menu; a click on
        // another tab header addresses that dockable, a click on the content the selected one
        setOnContextMenuRequested(event -> {
            Tab hit = tabHeaderAt(event.getScreenX(), event.getScreenY());
            Tab tab = hit != null ? hit : getSelectionModel().getSelectedItem();
            if (tab instanceof DockTab dockTab) {
                getSelectionModel().select(dockTab);
                ContextMenu menu = contextMenuFactory.apply(dockTab.dockable);
                if (menu != null) {
                    menu.show(this, event.getScreenX(), event.getScreenY());
                    event.consume();
                }
            }
        });
    }

    /**
     * @param screenX the screen x coordinate
     * @param screenY the screen y coordinate
     * @return the tab whose header contains the given screen position, or {@code null} (the tab
     *         header regions live in the skin; the lookup is defensive and yields {@code null}
     *         whenever the skin structure differs)
     */
    private Tab tabHeaderAt(double screenX, double screenY) {
        if (!(lookup(".tab-header-area > .headers-region") instanceof Parent headersRegion)) {
            return null;
        }
        int index = 0;
        for (Node header : headersRegion.getChildrenUnmodifiable()) {
            if (!header.getStyleClass().contains("tab")) {
                continue;
            }
            var bounds = header.localToScreen(header.getBoundsInLocal());
            if (bounds != null && bounds.contains(screenX, screenY)) {
                return index < getTabs().size() ? getTabs().get(index) : null;
            }
            index++;
        }
        return null;
    }

    /**
     * Registers the handler invoked when the user closes a tab via its close button. The handler
     * is responsible for removing the dockable from the workspace model.
     *
     * @param handler the handler, or {@code null} to disable
     */
    public void setOnDockableClosed(Consumer<Dockable> handler) {
        this.onDockableClosed = handler == null ? dockable -> {
        } : handler;
    }

    /**
     * Registers the handler invoked when the user double-clicks a tab (toggle maximize; see the
     * bibliothek double-click strategy cited above). {@link DockWorkspace} installs the handler.
     *
     * @param handler the handler, or {@code null} to disable
     */
    public void setOnMaximizeRequested(Consumer<Dockable> handler) {
        this.onMaximizeRequested = handler == null ? dockable -> {
        } : handler;
    }

    /**
     * Registers the factory building the context menu of the tabs. {@link DockWorkspace} installs
     * the factory.
     *
     * @param factory the factory, or {@code null} to disable the context menu
     */
    public void setContextMenuFactory(Function<Dockable, ContextMenu> factory) {
        this.contextMenuFactory = factory == null ? dockable -> null : factory;
    }

    /**
     * @param id the dockable id
     * @return whether a tab for the given dockable is present
     */
    public boolean contains(String id) {
        return tabByDockableId.containsKey(id);
    }

    /**
     * @return whether no tabs are shown
     */
    public boolean isEmpty() {
        return tabByDockableId.isEmpty();
    }

    /**
     * Adds a tab for the given dockable if it is not present yet.
     *
     * @param dockable the dockable to show
     * @return {@code true} if a tab was added, {@code false} if it was already present
     */
    public boolean addDockable(Dockable dockable) {
        if (tabByDockableId.containsKey(dockable.getId())) {
            return false;
        }
        DockTab tab = new DockTab(dockable, this);
        tab.setOnClosed(ignored -> onDockableClosed.accept(dockable));
        tabByDockableId.put(dockable.getId(), tab);
        getTabs().add(tab);
        if (getTabs().size() == 1) {
            getSelectionModel().select(0);
        }
        return true;
    }

    /**
     * Removes the tab of the given dockable.
     *
     * @param dockable the dockable to remove
     * @return {@code true} if a tab was present and has been removed
     */
    public boolean removeDockable(Dockable dockable) {
        return removeDockable(dockable.getId());
    }

    /**
     * Removes the tab with the given dockable id.
     *
     * @param id the dockable id
     * @return {@code true} if a tab was present and has been removed
     */
    public boolean removeDockable(String id) {
        Tab tab = tabByDockableId.remove(id);
        if (tab != null) {
            getTabs().remove(tab);
            return true;
        }
        return false;
    }

    /**
     * Selects the tab of the given dockable.
     *
     * @param id the dockable id
     */
    public void select(String id) {
        Tab tab = tabByDockableId.get(id);
        if (tab != null) {
            getSelectionModel().select(tab);
        }
    }

    /**
     * @return the dockable of the currently selected tab, if any
     */
    public Optional<Dockable> getSelectedDockable() {
        Tab selected = getSelectionModel().getSelectedItem();
        if (selected instanceof DockTab dockTab) {
            return Optional.of(dockTab.dockable);
        }
        return Optional.empty();
    }

    private static final class DockTab extends Tab {

        private final Dockable dockable;

        DockTab(Dockable dockable, DockTabPane pane) {
            this.dockable = dockable;
            Node content = dockable.getContent();
            setContent(content != null ? content : new StackPane());
            setGraphic(dockable.getIcon());
            textProperty().bind(dockable.titleProperty());
            graphicProperty().bind(dockable.iconProperty());
            closableProperty().bind(dockable.closableProperty());
        }
    }
}
