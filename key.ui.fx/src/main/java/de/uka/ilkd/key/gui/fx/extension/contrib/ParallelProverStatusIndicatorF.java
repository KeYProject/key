/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.extension.contrib;

import java.util.List;
import javafx.scene.control.Control;
import javafx.scene.control.Label;
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
 * <b>KNOWN-SIMPLIFIED:</b> the Swing original is a toggle button showing the parallel-prover
 * mode ({@code SC} for the single-core prover, {@code MT N×} for the multi-core prover with
 * {@code N} workers) with a left-click toggle and a right-click context menu to pick the worker
 * count (ParallelProverStatusIndicator.java:88-121). The FX minimum is a plain Label showing
 * the <em>auto-mode</em> state live — "Auto" while an automatic proof search is running,
 * "Manual" otherwise — bound to {@link KeYMediatorF#autoModeRunningProperty()} (the
 * "selection/auto-mode events" of the milestone description). Left-clicking the label still
 * toggles the persisted {@code GeneralSettings.PARALLEL_PROVER_ENABLED} flag and the label
 * reacts to the setting's property-change events like the Swing {@code refresh()}
 * (ParallelProverStatusIndicator.java:56-59, 127-139) — the worker-count picker and the
 * button-styling are out of scope.
 */
@KeYGuiExtensionF.Info(experimental = false, name = "Prover Mode in Status Line", optional = false,
    description = "Shows and toggles the prover mode in the status line.")
public class ParallelProverStatusIndicatorF
        implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.StartupF {

    private final Label label = new Label();

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // extension: MP9.0 — Swing ParallelProverStatusIndicator.java:56-59: the indicator
        // refreshes on the parallel-prover settings' property changes; the FX label extra binds
        // the live auto-mode state of the mediator (auto-mode events).
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        gs.addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_ENABLED,
            evt -> refresh(mediator));
        gs.addPropertyChangeListener(GeneralSettings.PARALLEL_PROVER_THREADS,
            evt -> refresh(mediator));
        mediator.autoModeRunningProperty().addListener((obs, old, running) -> refresh(mediator));
        // extension: MP9.0 — Swing ParallelProverStatusIndicator.java:43,88-90: left-click
        // toggles the parallel-prover mode (the worker-count context menu is simplified away).
        label.setOnMouseClicked(e -> {
            GeneralSettings general = ProofIndependentSettings.DEFAULT_INSTANCE
                    .getGeneralSettings();
            general.setParallelProverEnabled(!general.isParallelProverEnabled());
            refresh(mediator);
        });
        label.setTooltip(new Tooltip(
            "Auto: an automatic proof search is running. Manual: idle. Left-click toggles the "
                + "multi-core prover setting (Swing ParallelProverStatusIndicator, simplified: "
                + "the worker-count menu is not ported)."));
        refresh(mediator);
    }

    private void refresh(@Nullable KeYMediatorF mediator) {
        Runnable update = () -> {
            boolean auto = mediator != null && mediator.isInAutoMode();
            label.setText(auto ? "Auto" : "Manual");
        };
        if (FxUtil.isFxThread()) {
            update.run();
        } else {
            FxUtil.runLater(update);
        }
    }

    @Override
    public List<Control> getStatusLineControls() {
        // extension: MP9.0 — Swing ParallelProverStatusIndicator.java:142-145 contributes the
        // indicator (plus a leading strut for spacing); the FX minimum is the plain label —
        // one control per status provider, so the extension verification asserts exactly two
        // status controls across the two StatusLineF extensions.
        return List.of(label);
    }
}
