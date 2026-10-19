/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.plugins.caching.fx;

import javafx.scene.control.Button;
import javafx.scene.control.Tooltip;

import de.uka.ilkd.key.gui.fx.colors.ColorSettingsF;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.Nullable;

/**
 * The status-line button of the proof-caching extension, FX port of {@code ReferenceSearchButton}
 * (Swing ReferenceSearchButton.java:30-119). The button shows the number of goals of the selected
 * proof that are closed by reference ("Proof Caching (n)" coloured green) or a plain "Proof
 * Caching" label, is greyed out while the multi-core prover is active (single-core-only feature,
 * Swing ReferenceSearchButton.java:94-99) and disabled whenever no cached goals are present
 * (ReferenceSearchButton.java:114-118). The click behaviour (reference search + closing the
 * found goals) lives in {@link CachingExtensionF}; this class only renders the state.
 *
 * @author Arne Keller (Swing original)
 * @author MP9.1 status-line port (FX)
 */
final class CachingStatusButtonF extends Button {

    /**
     * Color used for the label if a reference is found (Swing {@code COLOR_FINE},
     * ReferenceSearchButton.java:34-37; the FX port registers the same colour key in the
     * {@link ColorSettingsF} palette).
     */
    private static final ColorSettingsF.ColorPropertyF COLOR_FINE = ColorSettingsF
            .define("caching.reference_found", "Color of the Proof Caching status line button "
                + "when references were found", ColorSettingsF.color(80, 120, 0));

    CachingStatusButtonF() {
        super("Proof Caching");
        setDisable(true);
    }

    /**
     * Update the UI state of this button (Swing {@code ReferenceSearchButton.updateState},
     * ReferenceSearchButton.java:93-119). Selection events may fire from the prover thread, so
     * the update is marshalled onto the FX thread.
     *
     * @param proof the currently selected proof
     */
    void updateState(@Nullable Proof proof) {
        Runnable update = () -> refresh(proof);
        if (FxUtil.isFxThread()) {
            update.run();
        } else {
            FxUtil.runLater(update);
        }
    }

    private void refresh(@Nullable Proof proof) {
        if (isMultiCoreActive()) {
            // single-core gate, Swing ReferenceSearchButton.java:94-99: the button greys out with
            // the shared tooltip while the multi-core prover is active
            setText("Proof Caching");
            setTextFill(null);
            setDisable(true);
            setTooltip(new Tooltip("Unavailable while the multi-core prover is active. "
                + "Switch to the single-core prover to use it."));
            return;
        }
        setTooltip(null);
        if (proof == null) {
            setText("Proof Caching");
            setTextFill(null);
            setDisable(true);
            return;
        }
        long foundRefs = proof.closedGoals().stream()
                .filter(g -> g.node().lookup(ClosedBy.class) != null).count();
        if (foundRefs > 0) {
            setText(String.format("Proof Caching (%d)", foundRefs));
            setTextFill(COLOR_FINE.getCurrentColor());
            setDisable(false);
        } else {
            setText("Proof Caching");
            setTextFill(null);
            setDisable(true);
        }
    }

    /**
     * @return whether the multi-core prover is active (Swing
     *         {@code SingleCoreFeatureGate.isActive} reads the same persisted setting)
     */
    private static boolean isMultiCoreActive() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isParallelProverEnabled();
    }
}
