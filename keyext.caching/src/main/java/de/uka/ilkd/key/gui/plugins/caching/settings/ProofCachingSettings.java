/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.settings;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the proof caching functionality.
 *
 * @author Arne Keller
 */
public class ProofCachingSettings extends AbstractPropertiesSettings {
    /**
     * When disposing a proof that is referenced elsewhere,
     * copy the steps to the references.
     */
    public static final String DISPOSE_COPY = "Copy steps into new proof";
    /**
     * When disposing a proof that is referenced elsewhere,
     * simply reopen the branches elsewhere.
     */
    public static final String DISPOSE_REOPEN = "Reopen proof";
    public static final String PRUNE_COPY = "Copy steps just before prune";
    public static final String PRUNE_REOPEN = "Reopen cached goal(s)";

    /**
     * Key ID for {@link #enabled}.
     */
    private static final String ENABLED_KEY = "Enabled";
    /**
     * Key ID for {@link #dispose}.
     */
    private static final String DISPOSE_KEY = "Dispose";
    /**
     * Key ID for {@link #prune}.
     */
    private static final String PRUNE_KEY = "Prune";
    /**
     * Key ID for {@link #autoAddClosedProofs}.
     */
    private static final String AUTO_ADD_CLOSED_KEY = "AutoAddClosed";


    /**
     * Whether proof caching is enabled.
     */
    private final AbstractPropertiesSettings.PropertyEntry<Boolean> enabled =
        createBooleanProperty(ENABLED_KEY, true);
    /**
     * Behaviour when disposing a proof that is referenced elsewhere.
     */
    private final AbstractPropertiesSettings.PropertyEntry<String> dispose =
        createStringProperty(DISPOSE_KEY, "");
    /**
     * Behaviour when pruning a proof that is referenced elsewhere.
     */
    private final AbstractPropertiesSettings.PropertyEntry<String> prune =
        createStringProperty(PRUNE_KEY, "");
    /**
     * Whether to automatically add closed proofs to the proof cache.
     */
    private final AbstractPropertiesSettings.PropertyEntry<Boolean> autoAddClosedProofs =
        createBooleanProperty(AUTO_ADD_CLOSED_KEY, false);

    public ProofCachingSettings() {
        super("ProofCaching");
    }

    public boolean getEnabled() {
        return enabled.get();
    }

    /**
     * Set whether proof caching is enabled.
     *
     * @param enabled value
     */
    public void setEnabled(boolean enabled) {
        this.enabled.set(enabled);
    }

    public String getDispose() {
        return dispose.get();
    }

    /**
     * Set the operation to be done when disposing a referenced proof.
     * Allowed operations: {@link #DISPOSE_COPY}, {@link #DISPOSE_REOPEN}.
     *
     * @param operation the operation
     */
    public void setDispose(String operation) {
        dispose.set(operation);
    }

    /**
     * Returns the current setting for behaviour when pruning into referenced branches.
     *
     * @return either an empty string, {@link #PRUNE_REOPEN} or {@link #PRUNE_COPY}
     */
    public String getPrune() {
        return prune.get();
    }

    /**
     * Set the operation to be done when a referenced proof is pruned.
     * Allowed operations: {@link #PRUNE_REOPEN}, {@link #PRUNE_COPY}.
     *
     * @param operation the operation
     */
    public void setPrune(String operation) {
        prune.set(operation);
    }

    /**
     * @return whether closed proofs should automatically be added to the proof caching database
     */
    public boolean getAutoAddClosedProofs() {
        return autoAddClosedProofs.get();
    }

    /**
     * Set whether proofs should automatically be added to the proof caching database.
     *
     * @param value whether to enable auto-caching
     */
    public void setAutoAddClosedProofs(boolean value) {
        autoAddClosedProofs.set(value);
    }
}
