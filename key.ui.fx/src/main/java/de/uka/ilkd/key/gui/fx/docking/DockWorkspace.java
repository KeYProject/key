/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.io.IOException;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

/**
 * The docking workspace of the JavaFX UI: three role areas (LEFT / MAIN / RIGHT) à la
 * {@code DockingHelper}'s {@code CGrid} roles of the Swing module {@code key.ui}, realized with
 * plain JavaFX {@link SplitPane} and {@link DockTabPane} widgets.
 * <p>
 * The workspace owns the model: an observable list of open {@link Dockable}s per role. The
 * {@link DockTabPane}s merely mirror that model. Dockables can be opened, closed, floated into
 * their own {@link Stage}, and the layout can be saved to / restored from a
 * {@link DockLayoutStore}.
 * <p>
 * Calling style (all methods) is the FX Application Thread via {@code Platform.runLater}, like
 * any UI mutation.
 */
public final class DockWorkspace {

    /**
     * An entry of the factory-default layout: open the given dockable in the given role.
     *
     * @param location the role area
     * @param dockable the dockable
     */
    public record Default(DockLocation location, Dockable dockable) {
    }

    /**
     * Recreates a dockable from its persisted id, e.g. a built-in view or an SPI panel.
     */
    @FunctionalInterface
    public interface DockableFactory {

        /**
         * @param id the persisted dockable id
         * @return the recreated dockable, or empty if the id is unknown
         */
        Optional<Dockable> create(String id);
    }

    private final EnumMap<DockLocation, DockTabPane> panes = new EnumMap<>(DockLocation.class);
    private final EnumMap<DockLocation, ObservableList<Dockable>> dockables =
        new EnumMap<>(DockLocation.class);
    private final Map<String, Stage> floatStages = new HashMap<>();

    private final SplitPane root = new SplitPane();

    private List<Default> defaultLayout = List.of();

    /**
     * Creates an empty workspace with three role areas.
     */
    public DockWorkspace() {
        root.getStyleClass().add("key-dock-workspace");
        for (DockLocation location : DockLocation.values()) {
            DockTabPane pane = new DockTabPane();
            pane.setOnDockableClosed(this::close);
            panes.put(location, pane);
            ObservableList<Dockable> list = FXCollections.observableArrayList();
            list.addListener(dockablesChanged(location));
            dockables.put(location, list);
        }
        root.getItems().addAll(panes.get(DockLocation.LEFT), panes.get(DockLocation.MAIN),
            panes.get(DockLocation.RIGHT));
        updateVisibility(DockLocation.LEFT);
        updateVisibility(DockLocation.RIGHT);
    }

    /**
     * @return the root node to embed in the application scene
     */
    public Node getRoot() {
        return root;
    }

    /**
     * @param location the role area
     * @return the tab pane presenting that role
     */
    public DockTabPane pane(DockLocation location) {
        return panes.get(location);
    }

    /**
     * @param location the role area
     * @return the observable model of the dockables open in that role
     */
    public ObservableList<Dockable> dockables(DockLocation location) {
        return dockables.get(location);
    }

    /**
     * @param id the dockable id
     * @return whether the dockable is currently open (in any role or floating)
     */
    public boolean isOpen(String id) {
        return find(id).isPresent();
    }

    /**
     * @param id the dockable id
     * @return the open dockable with the given id, if any
     */
    public Optional<Dockable> find(String id) {
        for (ObservableList<Dockable> list : dockables.values()) {
            for (Dockable dockable : list) {
                if (dockable.getId().equals(id)) {
                    return Optional.of(dockable);
                }
            }
        }
        return Optional.empty();
    }

    /**
     * @param id the dockable id
     * @return the role the dockable currently lives in
     */
    public Optional<DockLocation> locationOf(String id) {
        for (DockLocation location : DockLocation.values()) {
            for (Dockable dockable : dockables.get(location)) {
                if (dockable.getId().equals(id)) {
                    return Optional.of(location);
                }
            }
        }
        return Optional.empty();
    }

    /**
     * Opens the given dockable in the given role. If it is already open elsewhere (another role
     * or floating), it is moved; if it is already open in the requested role it is selected.
     *
     * @param dockable the dockable to open
     * @param location the target role
     */
    public void open(Dockable dockable, DockLocation location) {
        String id = dockable.getId();

        Stage floatStage = floatStages.remove(id);
        if (floatStage != null) {
            floatStage.close();
        }

        Optional<DockLocation> current = locationOf(id);
        if (current.isPresent()) {
            if (current.get() == location) {
                select(dockable);
                return;
            }
            dockables.get(current.get()).remove(dockable);
        }
        dockables.get(location).add(dockable);
        select(dockable);
    }

    /**
     * Closes the given dockable wherever it is open.
     *
     * @param dockable the dockable to close
     */
    public void close(Dockable dockable) {
        close(dockable.getId());
    }

    /**
     * Closes the dockable with the given id wherever it is open.
     *
     * @param id the dockable id
     */
    public void close(String id) {
        Stage floatStage = floatStages.remove(id);
        if (floatStage != null) {
            floatStage.close();
        }
        for (ObservableList<Dockable> list : dockables.values()) {
            list.removeIf(dockable -> dockable.getId().equals(id));
        }
    }

    /**
     * Selects the given dockable in its role.
     *
     * @param dockable the dockable to select
     */
    public void select(Dockable dockable) {
        locationOf(dockable.getId())
                .ifPresent(location -> panes.get(location).select(dockable.getId()));
    }

    /**
     * Floats the given dockable into its own undecorated-framed window. Closing the float window
     * closes the dockable. To re-dock, call {@link #open(Dockable, DockLocation)}.
     *
     * @param dockable the dockable to float
     */
    public void floatDockable(Dockable dockable) {
        String id = dockable.getId();
        locationOf(id).ifPresent(location -> dockables.get(location).remove(dockable));

        Stage floatStage = floatStages.get(id);
        if (floatStage != null) {
            floatStage.close();
        }
        Node content = dockable.getContent();
        Parent sceneRoot;
        if (content instanceof Parent parent) {
            sceneRoot = parent;
        } else {
            StackPane wrapper = new StackPane();
            if (content != null) {
                wrapper.getChildren().add(content);
            }
            sceneRoot = wrapper;
        }
        Scene scene = new Scene(sceneRoot);
        ThemeManager.getInstance().manage(scene);
        Stage stage = new Stage();
        stage.titleProperty().bind(dockable.titleProperty());
        stage.setScene(scene);
        stage.setOnCloseRequest(ignored -> close(id));
        floatStages.put(id, stage);
        stage.show();
    }

    /**
     * Sets the factory-default layout used by {@link #restoreFactoryDefault()}.
     *
     * @param layout the default dockables per role
     */
    public void setDefaultLayout(List<Default> layout) {
        this.defaultLayout = List.copyOf(layout);
    }

    /**
     * @return the factory-default layout currently registered
     */
    public List<Default> getDefaultLayout() {
        return defaultLayout;
    }

    /**
     * Closes everything and re-opens the factory-default layout.
     */
    public void restoreFactoryDefault() {
        closeAllFloating();
        for (ObservableList<Dockable> list : dockables.values()) {
            list.clear();
        }
        for (Default entry : defaultLayout) {
            open(entry.dockable(), entry.location());
        }
    }

    /**
     * Persists the current layout through the given store.
     *
     * @param store the store to write to
     * @throws IOException on I/O errors
     */
    public void saveLayout(DockLayoutStore store) throws IOException {
        EnumMap<DockLocation, List<String>> ids = new EnumMap<>(DockLocation.class);
        for (DockLocation location : DockLocation.values()) {
            ids.put(location,
                dockables.get(location).stream().map(Dockable::getId).toList());
        }
        store.save(ids);
    }

    /**
     * Restores a previously persisted layout. If the store contains no open dockables, the
     * factory-default layout is opened instead.
     *
     * @param store the store to read from
     * @param factory recreates dockables from their persisted ids
     * @throws IOException on I/O errors
     */
    public void restoreLayout(DockLayoutStore store, DockableFactory factory) throws IOException {
        Map<DockLocation, List<String>> saved = store.load();
        boolean anyOpen = saved.values().stream().anyMatch(list -> !list.isEmpty());

        closeAllFloating();
        for (ObservableList<Dockable> list : dockables.values()) {
            list.clear();
        }

        if (!anyOpen) {
            for (Default entry : defaultLayout) {
                open(entry.dockable(), entry.location());
            }
            return;
        }

        for (DockLocation location : DockLocation.values()) {
            for (String id : saved.getOrDefault(location, List.of())) {
                if (isOpen(id)) {
                    continue;
                }
                factory.create(id).ifPresent(dockable -> open(dockable, location));
            }
        }
    }

    private void closeAllFloating() {
        for (Stage stage : floatStages.values()) {
            stage.close();
        }
        floatStages.clear();
    }

    private ListChangeListener<Dockable> dockablesChanged(DockLocation location) {
        return change -> {
            while (change.next()) {
                for (Dockable dockable : change.getRemoved()) {
                    panes.get(location).removeDockable(dockable);
                }
                for (Dockable dockable : change.getAddedSubList()) {
                    panes.get(location).addDockable(dockable);
                }
            }
            updateVisibility(location);
        };
    }

    private void updateVisibility(DockLocation location) {
        if (location == DockLocation.MAIN) {
            return;
        }
        DockTabPane pane = panes.get(location);
        boolean empty = dockables.get(location).isEmpty();
        boolean visible = root.getItems().contains(pane);
        if (empty && visible) {
            root.getItems().remove(pane);
        } else if (!empty && !visible) {
            int index = location == DockLocation.LEFT ? 0 : root.getItems().size();
            root.getItems().add(Math.min(index, root.getItems().size()), pane);
        }
        applySensibleDividers();
    }

    private void applySensibleDividers() {
        int count = root.getItems().size();
        if (count >= 2) {
            double[] positions = count == 3 ? new double[] { 0.2, 0.8 } : new double[] { 0.25 };
            root.setDividerPositions(positions);
        }
    }
}
