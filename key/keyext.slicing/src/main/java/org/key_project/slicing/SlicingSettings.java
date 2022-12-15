package org.key_project.slicing;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class SlicingSettings extends AbstractPropertiesSettings {
    /**
     * Config key for {@link #aggressiveDeduplicate}.
     */
    private static final String KEY_AGGRESSIVE_DEDUPLICATE = "[ProofSlicing]aggressiveDeduplicate";
    /**
     * Aggressive rule deduplication config key.
     */
    private final PropertyEntry<Boolean> aggressiveDeduplicate =
        createBooleanProperty(KEY_AGGRESSIVE_DEDUPLICATE, true);

    /**
     * @return whether aggressive deduplication is turned on
     */
    public boolean getAggressiveDeduplicate() {
        return aggressiveDeduplicate.get();
    }

    /**
     * @param value whether to enable or disable this option
     */
    void setAggressiveDeduplicate(boolean value) {
        aggressiveDeduplicate.set(value);
    }
}
