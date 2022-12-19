package org.key_project.slicing;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

import java.util.Map;
import java.util.WeakHashMap;

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
    private final Map<Proof, Boolean> aggressiveDeduplicateOverride = new WeakHashMap<>();

    /**
     * @param proof proof
     * @return whether aggressive deduplication is turned on for this proof
     */
    public boolean getAggressiveDeduplicate(Proof proof) {
        if (aggressiveDeduplicateOverride.containsKey(proof)) {
            return aggressiveDeduplicate.get() && aggressiveDeduplicateOverride.get(proof);
        } else {
            return aggressiveDeduplicate.get();
        }
    }

    /**
     * Disable aggressive de-duplication for a particular proof.
     *
     * @param proof proof to disable aggresive de-duplication for
     */
    public void deactivateAggressiveDeduplicate(Proof proof) {
        aggressiveDeduplicateOverride.put(proof, false);
    }

    /**
     * @param value whether to enable or disable this option
     */
    void setAggressiveDeduplicate(boolean value) {
        aggressiveDeduplicate.set(value);
    }
}
