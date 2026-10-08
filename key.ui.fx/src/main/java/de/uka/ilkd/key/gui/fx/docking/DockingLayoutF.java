/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import java.io.IOException;
import java.util.ArrayList;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Menu;
import javafx.scene.control.MenuItem;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyEvent;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.docking.DockWorkspace.DockableFactory;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.keyshortcuts.KeyStrokeManagerF;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The FX counter-part of the Swing {@code key.ui} extension {@code
 * de.uka.ilkd.key.gui.docking.DockingLayout}: the <em>named layout slots</em> menu ({@code View >
 * Layout}), the global maximize toggle and the shutdown layout persistence.
 * <ul>
 * <li>Layout slots: the three Swing arrangements {@code Default}, {@code Slot 1}, {@code Slot 2}
 * are saved with <em>Ctrl+Shift+F10..F12</em> and loaded with <em>Ctrl+F10..F12</em> (Swing
 * {@code SaveLayoutAction}: {@code KeyStroke.getKeyStroke(key, SHORTCUT_KEY_MASK |
 * SHIFT_DOWN_MASK)}, {@code LoadLayoutAction}: {@code KeyStroke.getKeyStroke(key,
 * CTRL_DOWN_MASK)}; the defaults are registered in {@link KeyStrokeManagerF} under the Swing
 * action ids, so the shared {@code keystrokes.json} overrides apply).</li>
 * <li>Shutdown: the current arrangement is written to the {@code DockLayoutStore}, like the Swing
 * {@code GUIListener.shutDown} writing {@code CControl.writeXML}.</li>
 * <li>Maximize: <em>Ctrl+M</em> toggles the maximized state of the dockable focused by the user —
 * the bibliothek {@code CControl.KEY_MAXIMIZE_CHANGE} default ({@code KeyStroke.getKeyStroke(
 * VK_M, CTRL_MASK)}; the JavaFX equivalent of the "focused dockable" is the selected tab of the
 * {@link DockTabPane} containing the focus owner).</li>
 * </ul>
 * All menu labels and status-line messages follow the Swing original verbatim.
 */
public final class DockingLayoutF {

    private static final Logger LOGGER = LoggerFactory.getLogger(DockingLayoutF.class);

    /** The slot names of the Swing {@code DockingLayout.LAYOUT_NAMES}. */
    private static final String[] LAYOUT_NAMES = { DockLayoutStore.DEFAULT_SLOT, "Slot 1",
        "Slot 2" };

    /**
     * Dedicated slot of the {@code key.fx.verify.docking} self test; not part of the user
     * interface.
     */
    private static final String SELF_TEST_SLOT = "SelfTest";

    private final MainWindowF window;
    private final DockWorkspace workspace;
    private final DockLayoutStore store;

    private Scene scene;

    /** Creates the layout extension for the given main window (Swing: {@code init(MainWindow)}). */
    public DockingLayoutF(MainWindowF window) {
        this.window = window;
        this.workspace = window.getWorkspace();
        this.store = window.getLayoutStore();
    }

    /**
     * Installs the global parts: the Ctrl+M maximize toggle ({@code
     * CControl.KEY_MAXIMIZE_CHANGE}) as a scene filter and the shutdown persistence ({@code
     * GUIListener.shutDown}).
     *
     * @param scene the main window scene
     */
    public void install(Scene scene) {
        this.scene = scene;
        scene.addEventFilter(KeyEvent.KEY_PRESSED, this::handleKeyPressed);
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            try {
                workspace.saveLayout(store);
                LOGGER.info("Docking layout saved to {}", store.file());
            } catch (IOException e) {
                LOGGER.warn("Failed to save the docking layout", e);
            }
        }, "fx-docking-shutdown"));
    }

    /**
     * @return the {@code View > Layout} submenu with the Swing {@code DockingLayout
     * .getMainMenuActions} items (all load actions, then all save actions, then the reset).
     */
    public Menu layoutMenu() {
        Menu layout = new Menu("Layout");
        for (String name : LAYOUT_NAMES) {
            layout.getItems().add(layoutItem("Load " + name, name,
                "de.uka.ilkd.key.gui.docking.LoadLayoutAction$" + name,
                IconFactoryF.Key.OPEN_KEY_FILE, () -> loadLayout(name)));
        }
        for (String name : LAYOUT_NAMES) {
            layout.getItems().add(layoutItem("Save " + name, name,
                "de.uka.ilkd.key.gui.docking.SaveLayoutAction$" + name,
                IconFactoryF.Key.SAVE_FILE, () -> saveLayout(name)));
        }
        layout.getItems().add(layoutItem("Reset Layout", null, null, null, this::resetLayout));
        return layout;
    }

    /**
     * Creates one {@code View > Layout} item, registering its accelerator with the
     * {@link KeyStrokeManagerF} (Swing {@code setAcceleratorKey} + {@code
     * KeyStrokeManager.lookupAndOverride}), so user overrides from the shared {@code
     * keystrokes.json} apply.
     */
    private MenuItem layoutItem(String text, String slotName, String actionId,
            IconFactoryF.Key icon, Runnable action) {
        MenuItem item = new MenuItem(text);
        if (icon != null) {
            item.setGraphic(IconFactoryF.createIcon(icon));
        }
        if (actionId != null) {
            KeyStrokeManagerF manager = KeyStrokeManagerF.getInstance();
            manager.binding(actionId).ifPresent(item::setAccelerator);
            manager.register(item, actionId);
        }
        item.setOnAction(e -> action.run());
        return item;
    }

    /**
     * The Ctrl+M maximize toggle (bibliothek {@code CControl.KEY_MAXIMIZE_CHANGE}: "Change
     * maximize state" of the focused dockable).
     */
    private void handleKeyPressed(KeyEvent event) {
        if (event.getCode() == KeyCode.M && event.isControlDown() && !event.isShiftDown()
                && !event.isAltDown()) {
            event.consume();
            focusedPane().flatMap(DockTabPane::getSelectedDockable)
                    .ifPresent(workspace::toggleMaximize);
        }
    }

    /**
     * @return the tab pane containing the scene's focus owner, if any (the FX equivalent of the
     *         bibliothek "focused dockable")
     */
    private Optional<DockTabPane> focusedPane() {
        if (scene == null) {
            return Optional.empty();
        }
        Node node = scene.getFocusOwner();
        while (node != null) {
            if (node instanceof DockTabPane pane) {
                return Optional.of(pane);
            }
            node = node.getParent();
        }
        return Optional.empty();
    }

    /**
     * Loads the named slot into the workspace (Swing {@code LoadLayoutAction.actionPerformed});
     * an undefined slot keeps the current arrangement and reports it in the status line.
     */
    private void loadLayout(String name) {
        try {
            Optional<Map<DockLocation, List<String>>> saved = store.loadSlot(name);
            if (saved.isEmpty()) {
                LOGGER.info("Layout {} could not be found", name);
                window.setStatusLine("Layout " + name + " could not be found.");
                return;
            }
            workspace.restoreSlot(saved.get(), factory());
            LOGGER.info("Layout {} loaded", name);
            window.setStatusLine("Layout loaded from " + name);
        } catch (IOException e) {
            LOGGER.warn("Could not load layout {}", name, e);
        }
    }

    /**
     * Saves the current arrangement into the named slot (Swing {@code SaveLayoutAction
     * .actionPerformed}).
     */
    private void saveLayout(String name) {
        try {
            workspace.saveSlot(store, name);
            LOGGER.info("Layout {} saved", name);
            window.setStatusLine("Layout saved to " + name);
        } catch (IOException e) {
            LOGGER.warn("Could not save layout {}", name, e);
        }
    }

    /** The reset action (Swing {@code ResetLayoutAction}). */
    private void resetLayout() {
        workspace.restoreFactoryDefault();
        window.setStatusLine("Factory reset of the layout.");
    }

    private DockableFactory factory() {
        return id -> Optional.ofNullable(window.getDockables().get(id));
    }

    /**
     * Scripted self test ({@code key.fx.verify.docking}): exercises the docking interactions
     * ported from the Swing module — slot save/recall (Swing {@code SaveLayoutAction}/{@code
     * LoadLayoutAction}), maximize/restore (bibliothek {@code CMaximizeAction}) and close while
     * maximized — on the live workspace and compares the arrangements. Leaves the workspace in
     * the state it had before the test.
     *
     * @return {@code "PASS ..."} or {@code "FAIL: <failures>"}, like the other verify hooks
     */
    public String runSelfTest() {
        List<String> failures = new ArrayList<>();
        try {
            Map<DockLocation, List<String>> baseline = workspace.snapshotIds();
            Dockable sequent = window.getDockables().get(MainWindowF.ID_SEQUENT);

            // 1) named slots: save the arrangement, rearrange, recall, compare
            store.saveSlot(SELF_TEST_SLOT, baseline);
            workspace.close(MainWindowF.ID_SOURCE_VIEW);
            workspace.close(MainWindowF.ID_INFO_VIEW);
            if (workspace.isOpen(MainWindowF.ID_SOURCE_VIEW)) {
                failures.add("close did not hide the source view");
            }
            workspace.restoreSlot(store.loadSlot(SELF_TEST_SLOT).orElseThrow(), factory());
            if (!workspace.snapshotIds().equals(baseline)) {
                failures.add("slot recall did not restore the saved arrangement");
            }

            // 2) maximize/restore (bibliothek: the maximized dockable hides the others)
            if (workspace.isOpen(sequent.getId())) {
                workspace.maximize(sequent);
                if (workspace.snapshotIds().values().stream().mapToInt(List::size).sum() != 1
                        || !workspace.isMaximized(sequent.getId())) {
                    failures.add("maximize did not reduce the workspace to the one dockable");
                }
                workspace.restoreMaximized();
                if (!workspace.snapshotIds().equals(baseline)) {
                    failures.add("restore did not return the previous arrangement");
                }

                // 3) closing the maximized dockable restores the others (bibliothek behavior)
                workspace.maximize(sequent);
                workspace.close(sequent.getId());
                if (workspace.isMaximized(sequent.getId())) {
                    failures.add("closing the maximized dockable left the maximized state");
                }
                if (!workspace.snapshotIds().equals(without(baseline, sequent.getId()))) {
                    failures.add("closing the maximized dockable did not restore the others");
                }
            } else {
                failures.add("prerequisite: the sequent dockable is not open");
            }

            // bring the pre-test arrangement back
            workspace.restoreSlot(store.loadSlot(SELF_TEST_SLOT).orElseThrow(), factory());
            if (!workspace.snapshotIds().equals(baseline)) {
                failures.add("final slot recall did not restore the pre-test arrangement");
            }
        } catch (Exception e) {
            failures.add("unexpected exception: " + e);
        }
        return failures.isEmpty() ? "PASS (slots, maximize, restore, close-while-maximized)"
                : "FAIL: " + String.join("; ", failures);
    }

    private static Map<DockLocation, List<String>> without(Map<DockLocation, List<String>> ids,
            String dockableId) {
        EnumMap<DockLocation, List<String>> copy = new EnumMap<>(DockLocation.class);
        ids.forEach((location, list) -> copy.put(location,
            list.stream().filter(id -> !id.equals(dockableId)).toList()));
        return copy;
    }
}
