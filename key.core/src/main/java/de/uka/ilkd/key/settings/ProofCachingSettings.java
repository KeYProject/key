/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

/**
 * Settings for the proof caching functionality.
 *
 * @author Arne Keller
 */
public class ProofCachingSettings extends AbstractPropertiesSettings {
    public static final String DISPOSE_COPY = "Copy steps into new proof";
    public static final String DISPOSE_REOPEN = "Reopen proof";

    /**
     * Key ID for {@link #enabled}.
     */
    private static final String ENABLED_KEY = "[ProofCaching]Enabled";
    /**
     * Key ID for {@link #enabled}.
     */
    private static final String DISPOSE_KEY = "[ProofCaching]Dispose";


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
}
