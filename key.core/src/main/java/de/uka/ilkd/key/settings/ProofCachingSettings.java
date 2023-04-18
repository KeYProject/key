package de.uka.ilkd.key.settings;

/**
 * Settings for the proof caching functionality.
 *
 * @author Arne Keller
 */
public class ProofCachingSettings extends AbstractPropertiesSettings {
    private static final String ENABLED_KEY = "[ProofCaching]Enabled";

    /**
     * Whether proof caching is enabled.
     */
    private final AbstractPropertiesSettings.PropertyEntry<Boolean> enabled =
        createBooleanProperty(ENABLED_KEY, true);

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
}
