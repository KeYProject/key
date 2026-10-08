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
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.StackPane;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

    private static final Logger LOGGER = LoggerFactory.getLogger(DockWorkspace.class);

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
     * The dockable currently shown in the maximized mode (bibliothek {@code
     * ExtendedMode.MAXIMIZED}: the dockable fills the whole content area while the others keep
     * their positions and are merely hidden), or {@code null} if the workspace is not maximized.
     */
    private Dockable maximizedDockable;

    /**
     * The arrangement hidden by the maximized dockable: the open dockables per role and the
     * selected dockable per role, restored by {@link #restoreMaximized()} (bibliothek keeps the
     * "last maximized location" of a dockable in {@code MaximizedMode}).
     */
    private EnumMap<DockLocation, List<Dockable>> preMaximizedDockables;
    private EnumMap<DockLocation, String> preMaximizedSelection;

    /**
     * Creates an empty workspace with three role areas.
     */
    public DockWorkspace() {
        root.getStyleClass().add("key-dock-workspace");
        for (DockLocation location : DockLocation.values()) {
            DockTabPane pane = new DockTabPane();
            pane.setOnDockableClosed(this::close);
            // docking interactions ported from the Swing bibliothek framework:
            // double-click toggles maximize, the right-click popup offers the title actions
            pane.setOnMaximizeRequested(this::toggleMaximize);
            pane.setContextMenuFactory(this::createTabContextMenu);
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

        // bibliothek: making another dockable visible while one is maximized returns the
        // workspace to the normalized state (the maximized area covers the others otherwise)
        if (maximizedDockable != null && !maximizedDockable.getId().equals(id)) {
            restoreMaximized();
        }

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
        // bibliothek: closing the maximized dockable returns the workspace to the previous
        // arrangement (the hidden dockables reappear, the closed one is then removed below)
        if (maximizedDockable != null && maximizedDockable.getId().equals(id)) {
            restoreMaximized();
        }
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
        // bibliothek: externalizing returns the workspace to the normalized state first
        if (maximizedDockable != null && !maximizedDockable.getId().equals(id)) {
            restoreMaximized();
        }
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

    // ------------------------------------------------------------------
    // maximize (Swing bibliothek: ExtendedMode.MAXIMIZED / CMaximizeAction)
    // ------------------------------------------------------------------

    /**
     * @param id the dockable id
     * @return whether the dockable with the given id currently fills the whole workspace (the
     *         bibliothek {@code ExtendedMode.MAXIMIZED} state)
     */
    public boolean isMaximized(String id) {
        return maximizedDockable != null && maximizedDockable.getId().equals(id);
    }

    /**
     * @return the dockable currently shown maximized, if any
     */
    public Optional<Dockable> maximized() {
        return Optional.ofNullable(maximizedDockable);
    }

    /**
     * Toggles the maximized state of the given dockable (the bibliothek default double-click
     * strategy and {@code CControl.KEY_MAXIMIZE_CHANGE} switch between the normalized and the
     * maximized mode).
     *
     * @param dockable the dockable to toggle
     */
    public void toggleMaximize(Dockable dockable) {
        if (isMaximized(dockable.getId())) {
            restoreMaximized();
        } else {
            maximize(dockable);
        }
    }

    /**
     * Maximizes the given dockable: it fills the whole workspace while the other dockables are
     * hidden (their arrangement is remembered and brought back by {@link #restoreMaximized()},
     * like the bibliothek {@code CMaximizeAction} "Maximize" / {@code maximize.in}). Floating
     * dockables are not maximizable (bibliothek: the maximized mode is not available for
     * externalized dockables).
     *
     * @param dockable the dockable to maximize
     */
    public void maximize(Dockable dockable) {
        if (maximizedDockable == dockable) {
            return;
        }
        if (locationOf(dockable.getId()).isEmpty()) {
            LOGGER.info("Cannot maximize floating dockable {}", dockable.getId());
            return;
        }
        if (maximizedDockable != null) {
            restoreMaximized(); // maximize the other dockable from the restored arrangement
        }
        snapshotState();
        String id = dockable.getId();
        for (DockLocation location : DockLocation.values()) {
            dockables.get(location).removeIf(d -> !d.getId().equals(id));
        }
        select(dockable);
        maximizedDockable = dockable;
        LOGGER.info("Dockable '{}' maximized", id);
    }

    /**
     * Restores the arrangement hidden by {@link #maximize(Dockable)} (bibliothek {@code
     * CNormalizeAction}/{@code maximize.out} "Return": restores the former state). Does nothing
     * if the workspace is not maximized.
     */
    public void restoreMaximized() {
        if (maximizedDockable == null) {
            return;
        }
        maximizedDockable = null;
        closeAllFloating();
        for (DockLocation location : DockLocation.values()) {
            dockables.get(location).clear();
            for (Dockable dockable : preMaximizedDockables.get(location)) {
                dockables.get(location).add(dockable);
            }
        }
        for (DockLocation location : DockLocation.values()) {
            String selected = preMaximizedSelection.get(location);
            if (selected != null) {
                panes.get(location).select(selected);
            }
        }
        LOGGER.info("Maximized state restored");
    }

    private void snapshotState() {
        preMaximizedDockables = new EnumMap<>(DockLocation.class);
        preMaximizedSelection = new EnumMap<>(DockLocation.class);
        for (DockLocation location : DockLocation.values()) {
            preMaximizedDockables.put(location, List.copyOf(dockables.get(location)));
            preMaximizedSelection.put(location,
                panes.get(location).getSelectedDockable().map(Dockable::getId).orElse(null));
        }
    }

    // ------------------------------------------------------------------
    // tab context menu (the bibliothek title popup menu)
    // ------------------------------------------------------------------

    /**
     * Builds the context menu of a dock tab, the counter-part of the bibliothek title popup
     * menu: the dockable's custom title actions (Swing {@code DockingHelper.getTitleActions()}),
     * then the framework actions <em>Maximize</em> (or <em>Return</em> in the maximized state),
     * <em>Externalize</em> and <em>Close</em> (labels from the bibliothek resource bundle
     * {@code common.properties}: {@code maximize.in}/{@code maximize.out}, {@code
     * externalize.in}, {@code preference.shortcut.close.label}). Swing offers no "close others"
     * action and no <em>Minimize</em> equivalent exists in the FX role layout (the bibliothek
     * minimized bar has no port); both are omitted on purpose.
     *
     * @param dockable the dockable owning the clicked tab
     * @return the context menu to show
     */
    private ContextMenu createTabContextMenu(Dockable dockable) {
        ContextMenu menu = new ContextMenu();
        for (DockTitleActionF action : dockable.getTitleActions()) {
            MenuItem item = new MenuItem(action.text());
            item.setOnAction(e -> action.action().run());
            menu.getItems().add(item);
        }
        if (!dockable.getTitleActions().isEmpty()) {
            menu.getItems().add(new SeparatorMenuItem());
        }
        MenuItem maximizeItem = new MenuItem(isMaximized(dockable.getId()) ? "Return" : "Maximize");
        maximizeItem.setOnAction(e -> toggleMaximize(dockable));
        MenuItem externalizeItem = new MenuItem("Externalize");
        externalizeItem.setOnAction(e -> floatDockable(dockable));
        MenuItem closeItem = new MenuItem("Close");
        closeItem.setDisable(!dockable.isClosable());
        closeItem.setOnAction(e -> close(dockable));
        menu.getItems().addAll(maximizeItem, externalizeItem, closeItem);
        return menu;
    }

    // ------------------------------------------------------------------
    // named layout slots (Swing DockingLayout save/load actions)
    // ------------------------------------------------------------------

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
     * @return the ids of the currently open dockables per role (a snapshot of the model, e.g.
     *         for persisting the layout or comparing arrangements)
     */
    public Map<DockLocation, List<String>> snapshotIds() {
        EnumMap<DockLocation, List<String>> ids = new EnumMap<>(DockLocation.class);
        for (DockLocation location : DockLocation.values()) {
            ids.put(location,
                dockables.get(location).stream().map(Dockable::getId).toList());
        }
        return ids;
    }

    /**
     * Persists the current layout through the given store.
     *
     * @param store the store to write to
     * @throws IOException on I/O errors
     */
    public void saveLayout(DockLayoutStore store) throws IOException {
        store.save(snapshotIds());
    }

    /**
     * Saves the current arrangement into the named layout slot (Swing {@code SaveLayoutAction}:
     * {@code CControl.save(layoutName)}).
     *
     * @param store the store to write to
     * @param name the slot name ({@code Default}, {@code Slot 1}, ...)
     * @throws IOException on I/O errors
     */
    public void saveSlot(DockLayoutStore store, String name) throws IOException {
        store.saveSlot(name, snapshotIds());
    }

    /**
     * Restores a previously persisted layout. If neither the {@code Default} slot nor the
     * last-state layout contains open dockables, the factory-default layout is opened instead.
     * <p>
     * Like the Swing {@code DockingLayout.init}, the startup prefers the {@code Default} slot if
     * the user ever saved one ({@code setLayout(LAYOUT_NAMES[0])} applies it when defined); the
     * fallback to the plain last-state layout is the pre-existing FX behavior.
     *
     * @param store the store to read from
     * @param factory recreates dockables from their persisted ids
     * @throws IOException on I/O errors
     */
    public void restoreLayout(DockLayoutStore store, DockableFactory factory) throws IOException {
        Optional<Map<DockLocation, List<String>>> savedSlot =
            store.loadSlot(DockLayoutStore.DEFAULT_SLOT);
        Map<DockLocation, List<String>> saved = savedSlot.isPresent() ? savedSlot.get()
                : store.load();
        boolean anyOpen = saved.values().stream().anyMatch(list -> !list.isEmpty());

        if (!anyOpen) {
            closeAllFloating();
            for (ObservableList<Dockable> list : dockables.values()) {
                list.clear();
            }
            for (Default entry : defaultLayout) {
                open(entry.dockable(), entry.location());
            }
            return;
        }

        applyLayout(saved, factory);
    }

    /**
     * Restores the given named-slot arrangement (Swing {@code LoadLayoutAction}: {@code
     * CControl.load(layoutName)} — unlike {@link #restoreLayout} there is no factory-default
     * fallback; the caller checks that the slot is defined first).
     *
     * @param saved the ordered dockable ids per role to restore
     * @param factory recreates dockables from their persisted ids
     */
    public void restoreSlot(Map<DockLocation, List<String>> saved, DockableFactory factory) {
        applyLayout(saved, factory);
    }

    /**
     * Replaces the current arrangement with the given one (close everything, then re-open the
     * persisted dockables, skipping unknown ids — the FX counterpart of the Swing {@code
     * DockingHelper.restoreMissingPanels} completing a loaded layout).
     */
    private void applyLayout(Map<DockLocation, List<String>> saved, DockableFactory factory) {
        closeAllFloating();
        for (ObservableList<Dockable> list : dockables.values()) {
            list.clear();
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
