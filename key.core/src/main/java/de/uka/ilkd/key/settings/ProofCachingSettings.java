package de.uka.ilkd.key.settings;

/**
 * Settings for the proof caching functionality.
 *
 * @author Arne Keller
 */
public class ProofCachingSettings extends AbstractPropertiesSettings {
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

    public void setDispose(String operation) {
        dispose.set(operation);
    }
}
