/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Container;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import javax.swing.Action;

import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Single source of truth for greying out the <em>single-core-only</em> GUI contributions while the
 * multi-core prover is active (proof caching, proof slicing, ...).
 *
 * <p>
 * Instead of chasing every individual widget an extension adds, a feature registers the
 * single-core-only {@link Action} it contributes once via {@link #registerAutoDisabled(Action)}.
 * Disabling the action greys every toolbar button and menu item bound to it in lock-step with the
 * {@link GeneralSettings#PARALLEL_PROVER_ENABLED} setting, so a single registration covers all of
 * its UI.
 *
 * <p>
 * Components that manage their own enabled state (e.g. buttons whose availability depends on the
 * proof) cannot simply be registered; they consult {@link #isActive()} in their own update logic
 * and
 * may use {@link #setEnabledRecursively(Component, boolean)} as the shared disabling primitive.
 *
 */
public final class SingleCoreFeatureGate {

    /** Standard tooltip for a control disabled because the multi-core prover is active. */
    public static final String DISABLED_TOOLTIP =
        "Unavailable while the multi-core prover is active. "
            + "Switch to the single-core prover to use it.";

    /**
     * Actions disabled while the multi-core prover is active. Disabling the action greys every
     * toolbar button and menu item bound to it, so a single registration covers all of its UI.
     */
    private static final List<Action> REGISTERED_ACTIONS = new CopyOnWriteArrayList<>();

    static {
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().addPropertyChangeListener(
            GeneralSettings.PARALLEL_PROVER_ENABLED, evt -> refreshAll());
    }

    private SingleCoreFeatureGate() {}

    /**
     * @return whether the multi-core prover is active, i.e. the single-core-only features are
     *         currently unavailable
     */
    public static boolean isActive() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings()
                .isParallelProverEnabled();
    }

    /**
     * Registers a single-core-only {@link Action}; it is disabled (greying every toolbar button and
     * menu item bound to it) while the multi-core prover is active and re-enabled otherwise.
     *
     * @param action the action contributed by a single-core-only feature
     */
    public static void registerAutoDisabled(Action action) {
        REGISTERED_ACTIONS.add(action);
        action.setEnabled(!isActive());
    }

    /** Recursively sets the enabled state of {@code component} and all of its descendants. */
    public static void setEnabledRecursively(Component component, boolean enabled) {
        component.setEnabled(enabled);
        if (component instanceof Container container) {
            for (Component child : container.getComponents()) {
                setEnabledRecursively(child, enabled);
            }
        }
    }

    private static void refreshAll() {
        boolean enabled = !isActive();
        REGISTERED_ACTIONS.forEach(a -> a.setEnabled(enabled));
    }
}
