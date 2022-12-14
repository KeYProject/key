package org.key_project.slicing;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class SlicingSettings extends AbstractPropertiesSettings {
    public static final String KEY_AGGRESSIVE_DEDUPLICATE = "[ProofSlicing]aggressiveDeduplicate";
    private final PropertyEntry<Boolean> aggressiveDeduplicate =
        createBooleanProperty(KEY_AGGRESSIVE_DEDUPLICATE, true);

    public boolean getAggressiveDeduplicate() {
        return aggressiveDeduplicate.get();
    }

    public void setAggressiveDeduplicate(boolean value) {
        aggressiveDeduplicate.set(value);
    }
}
