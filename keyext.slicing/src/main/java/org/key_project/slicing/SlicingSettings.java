/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the proof slicing extension.
 *
 * @author Arne Keller
 */
public class SlicingSettings extends AbstractPropertiesSettings {

    public static final String CATEGORY = "ProofSlicing";

    /**
     * Config key for {@link #alwaysTrack}.
     */
    private static final String KEY_ALWAYS_TRACK = "alwaysTrack";
    /**
     * Config key for {@link #aggressiveDeduplicate}.
     */
    private static final String KEY_AGGRESSIVE_DEDUPLICATE = "aggressiveDeduplicate";
    /**
     * Config key for {@link #dotExecutable}.
     */
    private static final String KEY_DOT_EXECUTABLE = "dotExecutable";

    /**
     * Always track dependencies config key.
     */
    private final PropertyEntry<Boolean> alwaysTrack =
        createBooleanProperty(KEY_ALWAYS_TRACK, true);

    /**
     * Aggressive rule deduplication config key.
     */
    private final PropertyEntry<Boolean> aggressiveDeduplicate =
        createBooleanProperty(KEY_AGGRESSIVE_DEDUPLICATE, true);
    /**
     * Path to dot executable config key.
     */
    private final PropertyEntry<String> dotExecutable =
        createStringProperty(KEY_DOT_EXECUTABLE, "");

    /**
     * Override map for aggressive deduplication config.
     * If a proof is configured in this map, the value in this map will be preferred
     * over {@link #aggressiveDeduplicate}.
     */
    private final Map<Proof, Boolean> aggressiveDeduplicateOverride = new WeakHashMap<>();

    public SlicingSettings() {
        super(CATEGORY);
    }

    public boolean getAlwaysTrack() {
        return alwaysTrack.get();
    }

    public void setAlwaysTrack(boolean value) {
        alwaysTrack.set(value);
    }

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
     * @param proof proof to disable aggressive de-duplication for
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

    /**
     * @return path to the dot executable
     */
    public String getDotExecutable() {
        String path = dotExecutable.get();
        if (path != null && !path.isBlank()) {
            return path;
        }
        if (System.getProperty("os.name").startsWith("Windows")) {
            return "dot.exe";
        }
        return "dot";
    }

    /**
     * Set the path to the dot executable.
     *
     * @param path dot executable
     */
    public void setDotExecutable(String path) {
        dotExecutable.set(path);
    }
}
