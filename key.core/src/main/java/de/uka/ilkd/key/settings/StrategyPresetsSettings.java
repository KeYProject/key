/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Properties;

import de.uka.ilkd.key.strategy.StrategyProperties;

import org.jspecify.annotations.NonNull;

/**
 * User-defined strategy presets shown in the strategy options combo box.
 * <p>
 * In addition to the built-in presets (defined in code by the profile's
 * {@link de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition}), the user may store the
 * currently selected strategy options under a name and re-select them later. Each preset captures a
 * complete {@link StrategyProperties} value set together with the maximal number of rule
 * applications.
 * <p>
 * A single reserved preset named {@value #STASH_NAME} is used for the "stash current settings"
 * quick action: stashing again simply overwrites it.
 * <p>
 * Presets are persisted as part of the proof-independent settings. Persistence uses the
 * {@link Configuration} (JSON-like) format only; the deprecated flat {@link Properties} format is
 * not supported for presets (KeY writes the {@link Configuration} format on every save anyway).
 */
public class StrategyPresetsSettings extends AbstractSettings {
    /** Category / top-level key under which the presets are stored. */
    public static final String CATEGORY = "StrategyPresets";

    /** Name of the reserved single-slot stash preset. */
    public static final String STASH_NAME = "Stash";

    /** Property name fired whenever the set of presets changes. */
    public static final String PROP_PRESETS = "presets";

    /** Configuration key for a preset's display name. */
    private static final String KEY_NAME = "name";

    /** Configuration key for a preset's maximal rule applications. */
    private static final String KEY_MAX_STEPS = "maxSteps";

    /** Fallback max. rule applications if a stored preset lacks the entry. */
    private static final int DEFAULT_MAX_STEPS = 10000;

    /** The stored presets, in insertion order. */
    private final List<StrategyPreset> presets = new ArrayList<>();

    /**
     * A single named strategy preset.
     *
     * @param name display name; unique among the stored presets
     * @param maxSteps captured maximal number of rule applications
     * @param properties captured (complete) strategy properties
     */
    public record StrategyPreset(String name, int maxSteps, StrategyProperties properties) {
        public StrategyPreset {
            properties = (StrategyProperties) properties.clone();
        }

        @Override
        public StrategyProperties properties() {
            return (StrategyProperties) properties.clone();
        }
    }

    /**
     * @return an unmodifiable snapshot of the stored presets in insertion order
     */
    public List<StrategyPreset> getPresets() {
        return List.copyOf(presets);
    }

    /**
     * Looks up a preset by name.
     *
     * @param name the preset name
     * @return the preset, if present
     */
    public Optional<StrategyPreset> getPreset(String name) {
        return presets.stream().filter(p -> p.name().equals(name)).findFirst();
    }

    /**
     * @param name a preset name
     * @return {@code true} if a preset with the given name is stored
     */
    public boolean contains(String name) {
        return getPreset(name).isPresent();
    }

    /**
     * Adds a new preset or replaces an existing one with the same name. The preset keeps its
     * original position when replaced, otherwise it is appended.
     *
     * @param preset the preset to store
     */
    public void saveOrUpdate(StrategyPreset preset) {
        for (int i = 0; i < presets.size(); i++) {
            if (presets.get(i).name().equals(preset.name())) {
                presets.set(i, preset);
                firePropertyChange(PROP_PRESETS, null, preset.name());
                return;
            }
        }
        presets.add(preset);
        firePropertyChange(PROP_PRESETS, null, preset.name());
    }

    /**
     * Overwrites the reserved {@value #STASH_NAME} preset with the given settings.
     *
     * @param maxSteps the maximal number of rule applications to capture
     * @param properties the strategy properties to capture
     */
    public void stash(int maxSteps, StrategyProperties properties) {
        saveOrUpdate(new StrategyPreset(STASH_NAME, maxSteps, properties));
    }

    /**
     * Removes the preset with the given name (if present).
     *
     * @param name the preset name
     * @return {@code true} if a preset was removed
     */
    public boolean remove(String name) {
        if (presets.removeIf(p -> p.name().equals(name))) {
            firePropertyChange(PROP_PRESETS, name, null);
            return true;
        }
        return false;
    }

    /**
     * Renames a preset, keeping its position and captured settings.
     *
     * @param oldName the current name
     * @param newName the new name; must not already be in use by a different preset
     * @return {@code true} if the rename succeeded
     */
    public boolean rename(String oldName, String newName) {
        if (oldName.equals(newName)) {
            return true;
        }
        if (contains(newName)) {
            return false;
        }
        for (int i = 0; i < presets.size(); i++) {
            StrategyPreset p = presets.get(i);
            if (p.name().equals(oldName)) {
                presets.set(i, new StrategyPreset(newName, p.maxSteps(), p.properties()));
                firePropertyChange(PROP_PRESETS, oldName, newName);
                return true;
            }
        }
        return false;
    }

    @Override
    public void readSettings(@NonNull Configuration props) {
        presets.clear();
        List<Configuration> stored = props.getList(CATEGORY, Configuration.class);
        if (stored == null) {
            return;
        }
        for (Configuration entry : stored) {
            String name = entry.getString(KEY_NAME);
            if (name == null || name.isEmpty()) {
                continue;
            }
            int maxSteps = entry.getInt(KEY_MAX_STEPS, DEFAULT_MAX_STEPS);
            StrategyProperties properties = StrategyProperties.read(entry);
            presets.add(new StrategyPreset(name, maxSteps, properties));
        }
    }

    @Override
    public void writeSettings(@NonNull Configuration props) {
        List<Configuration> stored = new ArrayList<>(presets.size());
        for (StrategyPreset preset : presets) {
            Configuration entry = new Configuration();
            entry.set(KEY_NAME, preset.name());
            entry.set(KEY_MAX_STEPS, preset.maxSteps());
            preset.properties().write(entry);
            stored.add(entry);
        }
        props.set(CATEGORY, stored);
    }

    /**
     * Presets are only persisted via the {@link Configuration} format; the deprecated flat
     * {@link Properties} format cannot represent a list of presets and is intentionally not
     * supported here.
     */
    @Override
    public void readSettings(Properties props) {
        // intentionally empty: see class documentation
    }

    /**
     * Presets are only persisted via the {@link Configuration} format; the deprecated flat
     * {@link Properties} format cannot represent a list of presets and is intentionally not
     * supported here.
     */
    @Override
    public void writeSettings(Properties props) {
        // intentionally empty: see class documentation
    }
}
