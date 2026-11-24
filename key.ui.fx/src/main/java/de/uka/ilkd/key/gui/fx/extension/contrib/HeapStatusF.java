/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import javafx.geometry.Insets;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Control;
import javafx.scene.control.Label;
import javafx.scene.control.MenuItem;
import javafx.scene.control.ProgressBar;
import javafx.scene.control.Tooltip;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.StackPane;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Status-line extension showing an indication of the current heap consumption, FX port of
 * {@code de.uka.ilkd.key.gui.utilities.HeapStatusExt} (Swing HeapStatusExt.java:25-157).
 * <p>
 * The Swing original contributes one {@code HeapStatusComponent} — a {@code JProgressBar} of the
 * used vs. the maximum heap (HeapStatusExt.java:38-95): refreshed once at construction (:68) and
 * then every 5 seconds by a repeating Swing {@code Timer} (:69-71); the bar's maximum is
 * {@code Runtime.maxMemory()} in megabytes and its value the used heap
 * {@code totalMemory - freeMemory} in megabytes (:74-87), the painted string is
 * {@code "%sM of %sM"} of used and maximum megabytes (:87-88) and the tooltip an HTML table of
 * the max, free and total heap in MB (:89-94). The bar has no color logic: the value ratio is
 * the only dynamic state, the colors stay the LookAndFeel default. Any mouse click on the bar
 * triggers the Run-GC action (:50-55) and the popup menu ("Heap", :48-59) holds the items
 * "Open JConsole" (first) and "Run Gc" (:56-57). "Run Gc" runs {@code System.gc()}, logging the
 * total/max/free memory before and after (HeapStatusExt.java:97-115). "Open JConsole" looks up
 * {@code jconsole} next to {@code java.home}/bin (HeapStatusExt.java:141-154), launches it with
 * the current process id via {@code ProcessBuilder} (:130-139) and is disabled when the
 * executable is missing (:120-127).
 * <p>
 * The FX control keeps that surface: a button whose graphic is the progress bar with the Swing
 * string painting overlaid (a JavaFX {@code ProgressBar} has no string painting of its own), any
 * mouse click on it runs the GC (the right-click that opens the context menu also runs it,
 * exactly like the Swing {@code MouseAdapter} plus {@code setComponentPopupMenu}) and the
 * context menu holds the two items. The periodic refresh is a daemon
 * {@link ScheduledExecutorService} hopping to the FX thread via {@link FxUtil#runLater} (the
 * Swing {@code Timer} fired on the event dispatch thread the same way); the schedule is started
 * when the control enters the scene and stopped when it leaves, so no periodic task outlives the
 * UI element (the Swing {@code Timer} kept running forever).
 */
@KeYGuiExtensionF.Info(name = "Heap-Indicator",
    description = "Shows an indication of the current heap consumption in the status line of key",
    experimental = false)
@NullMarked
public final class HeapStatusF implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF {

    /**
     * The singleton status-line control (Swing {@code HeapStatusComponent}), created lazily on
     * first use — see {@link #statusLineComponent()}.
     */
    private @Nullable HeapStatusComponentF component;

    /**
     * @return the heap-status control (Swing {@code HeapStatusExt.getStatusLineComponents},
     *         HeapStatusExt.java:33-36); the same instance is returned on every call, so the
     *         host's status-bar membership check holds.
     */
    @Override
    public List<Control> getStatusLineControls() {
        // KNOWN-SIMPLIFIED: the control is created lazily on first use (the Swing original
        // constructs HeapStatusComponent eagerly, HeapStatusExt.java:33-36) — constructing
        // JavaFX controls requires the FX toolkit, but the SPI may instantiate the provider
        // before any display is up (headless unit tests); the host builds the status line at
        // startup, when the toolkit is already running (same rationale as the lazily-created
        // controls of keyext.caching.fx CachingExtensionF).
        return List.of(statusLineComponent());
    }

    /** @return the heap-status control, created on first use (lazy creation rationale above). */
    private HeapStatusComponentF statusLineComponent() {
        HeapStatusComponentF heapStatusComponent = component;
        if (heapStatusComponent == null) {
            heapStatusComponent = new HeapStatusComponentF();
            component = heapStatusComponent;
        }
        return heapStatusComponent;
    }

    /**
     * The heap status control (Swing {@code HeapStatusComponent}, a horizontal {@code Box} of
     * one {@code JProgressBar}, HeapStatusExt.java:38-95): the progress bar of the used vs. the
     * maximum heap with the Swing string painting overlaid, the click-to-GC behavior, the
     * right-click popup ("Open JConsole" + "Run Gc") and the periodic 5-second refresh.
     */
    private static class HeapStatusComponentF extends Button {

        private static final Logger LOGGER = LoggerFactory.getLogger(HeapStatusComponentF.class);

        /**
         * The shared daemon scheduler of the periodic heap refresh (Swing: a repeating
         * {@code javax.swing.Timer}, HeapStatusExt.java:69-71). One daemon thread serves every
         * heap-status control; the per-control task is cancelled when the control leaves the
         * scene (see the scene listener in the constructor), so the schedule stays empty and the
         * daemon thread never blocks the JVM exit.
         */
        private static final ScheduledExecutorService REFRESH_EXECUTOR = Executors
                .newSingleThreadScheduledExecutor(runnable -> {
                    Thread thread = new Thread(runnable, "heap-status-refresh");
                    thread.setDaemon(true);
                    return thread;
                });

        /** the heap bar (Swing {@code progressBar}, HeapStatusExt.java:41). */
        private final ProgressBar bar;

        /**
         * the string painting of the bar (Swing {@code setString}/{@code setStringPainted(true)},
         * HeapStatusExt.java:87-88 — JavaFX draws no string on a {@code ProgressBar}, so the
         * Swing string is overlaid on the bar).
         */
        private final Label stringLabel;

        /** the tooltip of the control (Swing {@code setToolTipText}, HeapStatusExt.java:89-94). */
        private final Tooltip tooltip;

        /**
         * the running periodic refresh task, {@code null} while the control is out of the scene
         * (the Swing {@code Timer} of the original ran forever instead, HeapStatusExt.java:69-71).
         */
        private @Nullable ScheduledFuture<?> refreshFuture;

        HeapStatusComponentF() {
            // Swing HeapStatusComponent (HeapStatusExt.java:61-72): the bar is added, the popup
            // menu is attached (setComponentPopupMenu + progressBar.setInheritsPopupMenu(true),
            // :64-66), the bar is updated once and the periodic 5-second timer is started
            // (:68-71). The Swing progressBar.setMaximumSize(100, 25) (:82) becomes the FX max
            // size of the bar graphic below.
            this.bar = new ProgressBar();
            this.bar.setMaxWidth(Double.MAX_VALUE);
            this.bar.setMaxHeight(Double.MAX_VALUE);
            this.stringLabel = new Label();
            StackPane graphic = new StackPane(this.bar, this.stringLabel);
            graphic.setPrefSize(100, 22);
            graphic.setMaxSize(100, 25);
            setGraphic(graphic);
            setPadding(Insets.EMPTY);

            this.tooltip = new Tooltip();
            setTooltip(this.tooltip);

            // Swing createPopupMenu (HeapStatusExt.java:48-59): every mouse click on the bar
            // runs the GC (the MouseAdapter fires on any mouse button, so the right-click that
            // also opens the popup runs the GC as well); the popup holds "Open JConsole" +
            // "Run Gc" (:56-57) and shows for the whole control incl. the bar
            // (setInheritsPopupMenu, :65-66). The event filter sees the click before the
            // button's own handlers consume it.
            addEventFilter(MouseEvent.MOUSE_CLICKED, e -> runGc());
            setContextMenu(createPopupMenu());

            update();

            // The refresh lifecycle (Swing: repeating Timer started in the constructor,
            // HeapStatusExt.java:69-71): the FX schedule is tied to the scene membership —
            // started when the control enters the scene, stopped when it leaves.
            // KNOWN-SIMPLIFIED: deliberate anti-leak deviation from the Swing original, whose
            // javax.swing.Timer keeps firing forever (it never stops, even after the component
            // leaves the UI).
            sceneProperty().addListener((obs, wasScene, scene) -> {
                if (scene != null) {
                    startRefresh();
                } else {
                    stopRefresh();
                }
            });
        }

        /**
         * Starts the periodic 5-second refresh (Swing {@code new Timer(5000, evt -> update())}
         * with {@code setRepeats(true)}/{@code start()}, HeapStatusExt.java:69-71): the schedule
         * fires on the daemon scheduler thread and hops to the FX thread for the bar update.
         */
        private void startRefresh() {
            if (refreshFuture != null) {
                return;
            }
            refreshFuture = REFRESH_EXECUTOR.scheduleAtFixedRate(() -> {
                try {
                    FxUtil.runLater(this::update);
                } catch (IllegalStateException e) {
                    // the FX toolkit is gone (application shutdown): stop the schedule instead
                    // of failing on every tick until the JVM exits
                    stopRefresh();
                    LOGGER.debug("Heap status refresh stopped: the FX toolkit is gone");
                }
            }, 5, 5, TimeUnit.SECONDS);
        }

        /** Stops the periodic refresh (cancels the scheduled task of this control). */
        private void stopRefresh() {
            ScheduledFuture<?> scheduled = refreshFuture;
            refreshFuture = null;
            if (scheduled != null) {
                scheduled.cancel(false);
            }
        }

        /**
         * Refreshes the bar from the current runtime memory state (Swing {@code update},
         * HeapStatusExt.java:74-95): the maximum is the maximum heap in MB, the value the used
         * heap ({@code totalMemory - freeMemory}) in MB, the string the Swing
         * {@code "%sM of %sM"} painting and the tooltip the max/free/total rows.
         */
        private void update() {
            Runtime rt = Runtime.getRuntime();
            final int mb = 1024 * 1024;

            int max = (int) (rt.maxMemory() / mb);
            int free = (int) (rt.freeMemory() / mb);
            int total = (int) (rt.totalMemory() / mb);

            int used = total - free;
            bar.setProgress(max > 0 ? (double) used / max : ProgressBar.INDETERMINATE_PROGRESS);
            stringLabel.setText("%sM of %sM".formatted(used, max));
            // KNOWN-SIMPLIFIED: the Swing tooltip is an HTML table (HeapStatusExt.java:89-94);
            // a JavaFX Tooltip renders plain text only, so the same max/free/total rows are
            // shown as a plain multi-line text.
            tooltip.setText("max %d MB\nfree %d MB\ntotal %d MB".formatted(max, free, total));
        }

        /**
         * The popup menu of the control (Swing {@code createPopupMenu}, HeapStatusExt.java:48-59):
         * "Open JConsole" first, then "Run Gc". The Swing popup's title "Heap"
         * (HeapStatusExt.java:49) is not rendered by Swing either, so no FX counterpart exists.
         */
        private ContextMenu createPopupMenu() {
            ContextMenu menu = new ContextMenu();
            menu.getItems().add(showMonitoringItem());
            menu.getItems().add(runGcItem());
            return menu;
        }

        /**
         * The "Run Gc" item (Swing {@code RunGcAction}, HeapStatusExt.java:97-115): logs the
         * memory state, runs {@code System.gc()} and logs again.
         */
        private MenuItem runGcItem() {
            MenuItem item = new MenuItem("Run Gc");
            item.setOnAction(e -> runGc());
            return item;
        }

        /**
         * Runs the garbage collector (Swing {@code RunGcAction.actionPerformed},
         * HeapStatusExt.java:102-114).
         */
        private void runGc() {
            Runtime rt = Runtime.getRuntime();
            LOGGER.info("Before GC: total {} MB, max {} MB, free {} MB",
                rt.totalMemory() / 1048576.0,
                rt.maxMemory() / 1048576.0,
                rt.freeMemory() / 1048576.0);
            System.gc();
            LOGGER.info("After GC: total {} MB, max {} MB, free {} MB",
                rt.totalMemory() / 1048576.0,
                rt.maxMemory() / 1048576.0,
                rt.freeMemory() / 1048576.0);
        }

        /**
         * The "Open JConsole" item (Swing {@code ShowMonitoringAction},
         * HeapStatusExt.java:117-155): launches {@code jconsole <pid>} with the current process
         * id; disabled when no {@code jconsole} executable is found next to {@code java.home}.
         */
        private MenuItem showMonitoringItem() {
            MenuItem item = new MenuItem("Open JConsole");
            String pathJConsole = findJConsole();
            if (pathJConsole == null) {
                item.setDisable(true);
                // KNOWN-SIMPLIFIED: the Swing original surfaces the missing executable as the
                // action's tooltip "Could not find `jconsole`, which is shipped by some
                // JREs/JDKs." (HeapStatusExt.java:124-126); JavaFX MenuItems have no tooltip,
                // so the message is logged instead.
                LOGGER.info("Open JConsole is disabled: could not find `jconsole`, which is "
                    + "shipped by some JREs/JDKs.");
            }
            item.setOnAction(e -> {
                if (pathJConsole != null) {
                    openJConsole(pathJConsole);
                }
            });
            return item;
        }

        /**
         * Launches {@code jconsole} for the current process (Swing
         * {@code ShowMonitoringAction.actionPerformed}, HeapStatusExt.java:130-139).
         */
        private void openJConsole(String pathJConsole) {
            long pid = ProcessHandle.current().pid();

            LOGGER.info("Execute jconsole: {} {}", pathJConsole, pid);
            try {
                new ProcessBuilder().command(pathJConsole, String.valueOf(pid)).start();
            } catch (IOException e) {
                // KNOWN-SIMPLIFIED: the Swing original shows a JOptionPane confirm dialog with
                // the exception message (HeapStatusExt.java:136-138), whose Yes/No/Cancel
                // result was never used; the FX port shows an error Alert with the message.
                String message = e.getMessage();
                new Alert(Alert.AlertType.ERROR, message != null ? message : e.toString())
                        .showAndWait();
            }
        }

        /**
         * Looks up the jconsole executable next to {@code java.home}/bin (Swing
         * {@code findJConsole}, HeapStatusExt.java:141-154).
         *
         * @return the executable path, or {@code null} when it is not shipped
         */
        private static @Nullable String findJConsole() {
            Path executableLinux = Paths.get(System.getProperty("java.home"), "bin", "jconsole");
            Path executableWindows =
                Paths.get(System.getProperty("java.home"), "bin", "jconsole.exe");

            if (Files.exists(executableLinux)) {
                return executableLinux.toString();
            }

            if (Files.exists(executableWindows)) {
                return executableWindows.toString();
            }
            return null;
        }
    }
}
