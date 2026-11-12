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

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Status-line indicator for the currently enabled keys of the tool-specific JML annotation
 * evaluation, FX port of {@code de.uka.ilkd.key.gui.JmlEnabledKeysIndicator} (Swing
 * JmlEnabledKeysIndicator.java:14-50).
 * <p>
 * The Swing original keeps a {@code JLabel} that shows the current
 * {@link GeneralSettings#getJmlEnabledKeys()} joined with {@code ", "} whenever the set differs
 * from {@link GeneralSettings#JML_ENABLED_KEYS_DEFAULT}, and is invisible otherwise
 * (JmlEnabledKeysIndicator.java:34-44); the tooltip is "Currently enabled keys for
 * tool-specific JML annotations" (JmlEnabledKeysIndicator.java:29) and a
 * {@code PropertyChangeListener} on {@link GeneralSettings#KEY_JML_ENABLED_KEYS} drives the
 * updates (JmlEnabledKeysIndicator.java:30). The port keeps the exact surface — same join, same
 * default-hiding, same tooltip text. The updates hop to the FX application thread
 * ({@link FxUtil#runLater}, the {@code Platform.runLater} counterpart), because the property
 * change events may fire from any thread (e.g. the settings reader at startup).
 * <p>
 * With the default key set ({@code key}) nothing in the FX UI edits
 * {@code GeneralSettings.JML_ENABLED_KEYS} yet — the indicator then simply stays invisible,
 * like the Swing original under the default; the setting can still be changed via the
 * {@code -PJML_ENABLED_KEYS=...} system property or the persisted configuration
 * (GeneralSettings.java:337-342).
 *
 * @see GeneralSettings#getJmlEnabledKeys()
 */
@KeYGuiExtensionF.Info(experimental = false,
    name = "JML Enabled Keys Indicator for the Status Line")
@NullMarked
public final class JmlEnabledKeysIndicatorF
        implements KeYGuiExtensionF, KeYGuiExtensionF.StatusLineF, KeYGuiExtensionF.StartupF {

    /**
     * The tooltip of the indicator (Swing {@code setToolTipText}, JmlEnabledKeysIndicator.java:29).
     */
    private static final String TOOLTIP =
        "Currently enabled keys for tool-specific JML annotations";

    /** The observed settings (Swing {@code settings}, JmlEnabledKeysIndicator.java:23-24). */
    private final GeneralSettings settings =
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

    /**
     * The indicator label (Swing {@code lblIndicator}, JmlEnabledKeysIndicator.java:25), created
     * lazily on first contribution. KNOWN-SIMPLIFIED: instantiation is deferred because
     * constructing JavaFX controls requires the FX toolkit, but the SPI may instantiate the
     * provider before any display is up (headless unit tests, verify hooks); the host builds the
     * status line at startup, when the toolkit is already running (see
     * {@code CachingExtensionF.menuToggleItem} in {@code keyext.caching.fx} for the same
     * decision). For the same reason the Swing constructor's property-listener registration
     * (JmlEnabledKeysIndicator.java:30) is deferred to the {@link #init} hook.
     */
    private @Nullable Label lblIndicator;

    @Override
    public List<Control> getStatusLineControls() {
        Label label = lblIndicator;
        if (label == null) {
            // Swing lblIndicator (JmlEnabledKeysIndicator.java:25) plus the constructor surface
            // (JmlEnabledKeysIndicator.java:28-31): the tooltip and the initial update. The
            // Swing EmptyBorder(5, 5, 5, 5) (:28) was the Swing status line's spacing; the FX
            // status bar pads and baseline-aligns its controls itself
            // (MainWindowF.buildStatusBar), so the label is contributed bare — one control per
            // status provider (cf. ParallelProverStatusIndicatorF).
            label = new Label();
            label.setTooltip(new Tooltip(TOOLTIP));
            lblIndicator = label;
            update();
        }
        // Swing getStatusLineComponents (JmlEnabledKeysIndicator.java:46-49): the singleton label
        return List.of(label);
    }

    @Override
    public void init(MainWindowF window, KeYMediatorF mediator) {
        // Swing constructor (JmlEnabledKeysIndicator.java:30): the label refreshes on
        // GeneralSettings.KEY_JML_ENABLED_KEYS property changes; the initial update (:31) is
        // issued next to the one of getStatusLineControls (idempotent, ordering-agnostic).
        settings.addPropertyChangeListener(GeneralSettings.KEY_JML_ENABLED_KEYS, it -> update());
        update();
    }

    /**
     * Refreshes the label from the live setting (Swing {@code update},
     * JmlEnabledKeysIndicator.java:34-44): the joined keys while the set differs from
     * {@link GeneralSettings#JML_ENABLED_KEYS_DEFAULT}, empty and invisible otherwise. Off-thread
     * calls (the property change events may fire from any thread) are marshalled to the FX
     * application thread.
     */
    private void update() {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(this::update);
            return;
        }
        Label label = lblIndicator;
        if (label == null) {
            // not contributed yet; the state is recomputed on contribution and in init
            return;
        }
        final var current = settings.getJmlEnabledKeys();
        if (!GeneralSettings.JML_ENABLED_KEYS_DEFAULT.equals(current)) {
            label.setText(String.join(", ", current));
            label.setVisible(true);
        } else {
            label.setText("");
            label.setVisible(false);
        }
    }

    /** @return the observed settings (package-private for the toolkit-free unit test) */
    GeneralSettings settings() {
        return settings;
    }
}
