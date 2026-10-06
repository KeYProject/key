/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Consumer;

import javafx.scene.Node;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
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

    public DockTabPane() {
        getStyleClass().add("key-dock-tab-pane");
        setTabDragPolicy(TabDragPolicy.REORDER);
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
        DockTab tab = new DockTab(dockable);
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

        DockTab(Dockable dockable) {
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
