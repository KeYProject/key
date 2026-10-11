/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import java.util.TreeSet;
import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.scene.control.Button;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Control;
import javafx.scene.control.MenuItem;
import javafx.scene.control.RadioMenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;

/**
 * Status-line indicator for the prover state, FX port of {@code
 * de.uka.ilkd.key.gui.extension.impl.ParallelProverStatusIndicator} (Swing
 * ParallelProverStatusIndicator.java:34-145).
 * <p>
 * The Swing original is a toggle button showing the parallel-prover mode ({@code SC} for the
 * single-core prover, {@code MT Nx} for the multi-core prover with {@code N} workers) with a
 * left-click toggle and a right-click context menu to pick the worker count
 * (ParallelProverStatusIndicator.java:88-121): the menu holds the "Single-core" radio item, a
 * separator and one "Multi-core, N workers" radio item per offered count — the set
 * {@code {2, 4, 8, cores}} capped to the available processors
 * (ParallelProverStatusIndicator.java:106-119); picking a count writes the worker count and
 * enables the parallel prover. The button reads and writes the same
 * {@link GeneralSettings#PARALLEL_PROVER_ENABLED} setting as the preference pane and reacts to
 * the setting's property-change events like the Swing {@code refresh()}
 * (ParallelProverStatusIndicator.java:56-59, 127-139). The button keeps a constant size
 * regardless of the shown label (Swing {@code fixSize}, :77-86) — in JavaFX the button reserves
 * the width of the widest possible label via {@code min/maxWidth}, the FX counterpart.
 * <p>
 * The earlier FX minimum (a plain "Auto"/"Manual" label bound to the mediator's auto-mode
 * events) is folded into the button tooltip: the tooltip now leads with the live auto-mode state
 * before the Swing mode hints, so the auto-mode indication of the previous port is kept without
 * regressing the Swing button surface.
 */
@KeYGuiExtensionF.Info(experimental = false, name = "Prover Mode in Status Line", optional = false,
    description = "Shows and toggles the single-core / multi-core prover mode in the status line.")
public class ParallelProverStatusIndicatorF
        implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.StartupF {

    /** The toggle button (Swing {@code ParallelProverStatusIndicator.button}). */
    private final Button button = new Button();

    /** the auto-mode state of the mediator, {@code null} until {@link #init} (tooltip only). */
    private @Nullable ReadOnlyBooleanProperty autoMode;

    public ParallelProverStatusIndicatorF() {
        // Swing fixSize (ParallelProverStatusIndicator.java:77-86): keep the button a constant
        // size regardless of whether "SC" or "MT Nx" is shown, by sizing it for the widest label
        button.getStyleClass().add("prover-mode-button");
        button.setMinWidth(58);
        button.setMaxWidth(58);
        button.setOnAction(e -> toggleMode());
        // Swing maybeShowMenu (ParallelProverStatusIndicator.java:92-121): the right-click popup
        // is rebuilt per showing (the radio states follow the live settings); shown explicitly
        // from the context-menu-request event (no persistent setContextMenu, whose automatic
        // showing would race the rebuild)
        button.setOnContextMenuRequested(e -> {
            ContextMenu menu = popupMenu != null ? popupMenu : new ContextMenu();
            menu.getItems().setAll(buildMenu().getItems());
            popupMenu = menu;
            if (!menu.isShowing()) {
                menu.show(button, e.getScreenX(), e.getScreenY());
            }
        });
    }

    /** the right-click worker-count menu (Swing {@code maybeShowMenu}, :92-121). */
    private @Nullable ContextMenu popupMenu;

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // Swing init (ParallelProverStatusIndicator.java:42-62): the button refreshes on the
        // parallel-prover settings' property changes; the tooltip keeps the FX auto-mode state
        // of the earlier port live via the mediator.
        GeneralSettings gs = generalSettings();
        gs.addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_ENABLED, evt -> refresh());
        gs.addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_THREADS, evt -> refresh());
        autoMode = mediator.autoModeRunningProperty();
        autoMode.addListener((obs, was, running) -> refresh());
        refresh();
    }

    private static GeneralSettings generalSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
    }

    private static int cores() {
        return Math.max(1, Runtime.getRuntime().availableProcessors());
    }

    /**
     * The effective worker count (Swing {@code effectiveThreads},
     * ParallelProverStatusIndicator.java:123-125).
     */
    private static int effectiveThreads(GeneralSettings gs) {
        return Math.max(1, Math.min(gs.getParallelProverThreadCount(), cores()));
    }

    /** Toggles the parallel-prover mode (Swing {@code toggleMode}, :88-90). */
    private void toggleMode() {
        generalSettings().setParallelProverEnabled(!generalSettings().isParallelProverEnabled());
    }

    /**
     * Builds the worker-count menu of the button (Swing {@code maybeShowMenu},
     * ParallelProverStatusIndicator.java:92-121): the "Single-core" radio item, a separator and
     * one "Multi-core, N workers" radio item per offered count — the set {@code {2, 4, 8, cores}}
     * capped to the available processors.
     */
    private ContextMenu buildMenu() {
        GeneralSettings gs = generalSettings();
        ContextMenu menu = new ContextMenu();
        RadioMenuItem single = new RadioMenuItem("Single-core");
        single.setSelected(!gs.isParallelProverEnabled());
        single.setOnAction(a -> gs.setParallelProverEnabled(false));
        menu.getItems().add(single);
        menu.getItems().add(new SeparatorMenuItem());

        // Offer a small, sensible set of worker counts capped at the available processors.
        TreeSet<Integer> counts = new TreeSet<>(List.of(2, 4, 8, cores()));
        for (Integer n : counts) {
            if (n < 2 || n > cores()) {
                continue;
            }
            RadioMenuItem item = new RadioMenuItem("Multi-core, " + n + " workers");
            item.setSelected(gs.isParallelProverEnabled() && effectiveThreads(gs) == n);
            item.setOnAction(a -> {
                gs.setParallelProverThreadCount(n);
                gs.setParallelProverEnabled(true);
            });
            menu.getItems().add(item);
        }
        return menu;
    }

    /** Refreshes the button label and tooltip (Swing {@code refresh}, :127-139). */
    private void refresh() {
        Runnable update = () -> {
            GeneralSettings gs = generalSettings();
            boolean auto = autoMode != null && autoMode.get();
            String autoHint = auto ? "Auto mode running. " : "Idle. ";
            if (gs.isParallelProverEnabled()) {
                int threads = effectiveThreads(gs);
                button.setText("MT " + threads + "x");
                button.setTooltip(new Tooltip(autoHint + "Multi-core prover active (" + threads
                    + " workers). Left-click for single-core; right-click to choose the "
                    + "worker count."));
            } else {
                button.setText("SC");
                button.setTooltip(new Tooltip(autoHint + "Single-core prover active. Left-click "
                    + "for multi-core; right-click to choose the worker count."));
            }
        };
        if (FxUtil.isFxThread()) {
            update.run();
        } else {
            FxUtil.runLater(update);
        }
    }

    /**
     * extensions (WP-3): headless self test of the indicator (asserted by {@code
     * key.fx.verify.extensions}): the Swing-parity button surface — the "SC" label while the
     * parallel prover is disabled, the "MT Nx" label while it is enabled with the effective
     * worker count, the left-click toggle through the real {@code onAction} handler flipping
     * {@code GeneralSettings.PARALLEL_PROVER_ENABLED}, and the right-click worker-count menu
     * (the "Single-core" radio plus one "Multi-core, N workers" radio per offered count, capped
     * to the available processors; picking a count writes the thread count and enables the
     * parallel prover). The previous settings are restored afterwards.
     *
     * @return a one-line report, {@code "... PASS"} if every assertion holds
     */
    public String verifyProverMode() {
        if (!FxUtil.isFxThread()) {
            return FxUtil.callAndWait(this::verifyProverMode);
        }
        GeneralSettings gs = generalSettings();
        boolean enabled = gs.isParallelProverEnabled();
        int threads = gs.getParallelProverThreadCount();
        boolean pass = true;
        try {
            // the "SC" leg: disabled parallel prover, left-click toggle through the real handler
            gs.setParallelProverEnabled(false);
            pass &= "SC".equals(button.getText());
            button.getOnAction().handle(null);
            pass &= gs.isParallelProverEnabled() && button.getText().startsWith("MT ");
            button.getOnAction().handle(null);
            pass &= !gs.isParallelProverEnabled() && "SC".equals(button.getText());

            // the right-click menu: radio items + the pick-a-count action
            ContextMenu menu = buildMenu();
            pass &= menu.getItems().stream()
                    .anyMatch(it -> it instanceof RadioMenuItem
                            && "Single-core".equals(((RadioMenuItem) it).getText()));
            List<MenuItem> counts = menu.getItems().stream()
                    .filter(it -> it instanceof RadioMenuItem && it.getText() != null
                            && it.getText().startsWith("Multi-core, "))
                    .toList();
            pass &= !counts.isEmpty();
            int offered = counts.stream()
                    .mapToInt(it -> Integer.parseInt(it.getText().replaceAll("\\D", "")))
                    .max().orElse(0);
            pass &= offered <= cores();
            counts.get(counts.size() - 1).fire();
            pass &= gs.isParallelProverEnabled()
                    && gs.getParallelProverThreadCount() == offered
                    && button.getText().equals("MT " + effectiveThreads(gs) + "x");
        } finally {
            gs.setParallelProverThreadCount(threads);
            gs.setParallelProverEnabled(enabled);
        }
        return "button[" + button.getText() + "] counts=" + menu2Counts() + " "
            + (pass ? "PASS" : "FAIL");
    }

    /** the offered worker counts of the menu (report helper of {@link #verifyProverMode}). */
    private String menu2Counts() {
        return buildMenu().getItems().stream()
                .map(MenuItem::getText)
                .filter(text -> text != null && text.startsWith("Multi-core, "))
                .map(text -> text.substring("Multi-core, ".length()))
                .reduce((a, b) -> a + "," + b)
                .orElse("-");
    }

    @Override
    public List<Control> getStatusLineControls() {
        // Swing getStatusLineComponents (ParallelProverStatusIndicator.java:141-145): the
        // indicator button plus a leading strut for spacing; the FX status line spaces its
        // controls, so only the button is contributed — one control per status provider.
        return List.of(button);
    }
}
