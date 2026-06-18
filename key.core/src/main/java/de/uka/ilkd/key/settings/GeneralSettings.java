/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class GeneralSettings extends AbstractSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(GeneralSettings.class);

    /**
     * This parameter disables the possibility to prune in closed branches. It is meant as a
     * fallback solution if storing all closed goals needs too much memory or is not needed. Pruning
     * is disabled as a default (for command-line mode, tests, ...) and explicitly has to be enabled
     * for interactive mode.
     */
    public static boolean noPruningClosed = true;

    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary directories (can be
     * used for debugging).
     */
    public static boolean keepFileRepos = false;

    /**
     * if true then JML specifications are globally disabled in this run of KeY, regardless of the
     * regular settings
     */
    public static boolean disableSpecs = false;

    private static final String CATEGORY = "General";

    public static final String TACLET_FILTER = "StupidMode";
    public static final String DND_DIRECTION_SENSITIVE_KEY = "DnDDirectionSensitive";
    public static final String USE_JML_KEY = "UseJML";

    public static final String KEY_JML_ENABLED_KEYS = "JML_ENABLED_KEYS";

    public static final String RIGHT_CLICK_MACROS_KEY = "RightClickMacros";
    public static final String AUTO_SAVE = "AutoSavePeriod";

    /**
     * The key for storing the ensureSourceConsistency flag in settings
     */
    private static final String ENSURE_SOURCE_CONSISTENCY = "EnsureSourceConsistency";

    /** Whether automatic proof search uses the multi-core (parallel) prover. */
    public static final String PARALLEL_PROVER_ENABLED = "ParallelProverEnabled";
    /** The number of worker threads the multi-core prover uses. */
    public static final String PARALLEL_PROVER_THREADS = "ParallelProverThreadCount";

    /** Default worker count when the multi-core prover is first enabled. */
    public static final int PARALLEL_PROVER_THREADS_DEFAULT = 4;

    /** Default value for {@link #getJmlEnabledKeys()} */
    public static final Set<String> JML_ENABLED_KEYS_DEFAULT = Set.of("key");

    private Set<String> jmlEnabledKeys = new TreeSet<>(JML_ENABLED_KEYS_DEFAULT);

    /**
     * minimize interaction is on by default
     */
    private boolean tacletFilter = true;

    /**
     * is drag and drop instantiation direction sensitive
     */
    private boolean dndDirectionSensitive = true;

    /**
     * launches the rightclick the macro menu. on by default.
     */
    private boolean rightClickMacros = true;

    /**
     * JML is active by default
     */
    private boolean useJML = true;

    /**
     * auto save is disabled by default. Positive values indicate save period.
     */
    private int autoSave = 0;

    /**
     * If enabled, source files are cached at first use to ensure consistency between proof and
     * source code. Toggles between SimpleFilerepo (false) and DiskFileRepo (true).
     */
    private boolean ensureSourceConsistency = true;

    /**
     * Whether automatic proof search uses the multi-core (parallel) prover instead of the legacy
     * single-threaded one. Single-core is the safe fallback and keeps the single-core-only features
     * (proof caching, slicing, merge rule, ...) available.
     * <p>
     * Enabled by default in this pull-request build so the multi-core prover is easy to try; this
     * is
     * to be reverted to {@code false} (single-core) when the change is accepted for {@code main}.
     */
    private boolean parallelProverEnabled = true;

    /**
     * Number of worker threads for the multi-core prover. Only relevant when
     * {@link #parallelProverEnabled} is set; the effective count is clamped to the available
     * processors.
     */
    private int parallelProverThreadCount = PARALLEL_PROVER_THREADS_DEFAULT;

    GeneralSettings() {
        // addSettingsListener(AutoSaver.settingsListener);
    }

    public Set<String> getJmlEnabledKeys() {
        return jmlEnabledKeys;
    }

    public void setJmlEnabledKeys(Set<String> jmlEnabledKeys) {
        var oldValue = this.jmlEnabledKeys;
        this.jmlEnabledKeys = Objects.requireNonNull(jmlEnabledKeys);
        firePropertyChange(KEY_JML_ENABLED_KEYS, oldValue, jmlEnabledKeys);
    }

    public boolean getTacletFilter() {
        return tacletFilter;
    }

    public boolean isDndDirectionSensitive() {
        return dndDirectionSensitive;
    }

    public boolean isRightClickMacro() {
        return rightClickMacros;
    }

    public boolean isUseJML() {
        return useJML && !disableSpecs;
    }

    public int autoSavePeriod() {
        return autoSave;
    }

    public boolean isEnsureSourceConsistency() {
        return ensureSourceConsistency;
    }

    /**
     * @return whether automatic proof search uses the multi-core (parallel) prover
     */
    public boolean isParallelProverEnabled() {
        return parallelProverEnabled;
    }

    /**
     * @return the configured number of worker threads for the multi-core prover (not yet clamped to
     *         the available processors)
     */
    public int getParallelProverThreadCount() {
        return parallelProverThreadCount;
    }

    // setter
    public void setTacletFilter(boolean b) {
        var old = tacletFilter;
        tacletFilter = b;
        firePropertyChange(TACLET_FILTER, old, b);
    }

    public void setDnDDirectionSensitivity(boolean b) {
        var old = dndDirectionSensitive;
        dndDirectionSensitive = b;
        firePropertyChange(DND_DIRECTION_SENSITIVE_KEY, old, dndDirectionSensitive);
    }

    public void setRightClickMacros(boolean b) {
        var old = rightClickMacros;
        rightClickMacros = b;
        firePropertyChange(RIGHT_CLICK_MACROS_KEY, old, rightClickMacros);
    }

    public void setUseJML(boolean b) {
        var old = useJML;
        useJML = b;
        firePropertyChange(USE_JML_KEY, old, useJML);
    }

    public void setAutoSave(int period) {
        var old = autoSave;
        autoSave = period;
        firePropertyChange(AUTO_SAVE, old, autoSave);
    }

    /**
     * Sets the ensureSourceConsistency flag. This enables/disables caching of source files at first
     * use via a FileRepo.
     *
     * @param b the new truth value of the flag
     */
    public void setEnsureSourceConsistency(boolean b) {
        var old = ensureSourceConsistency;
        ensureSourceConsistency = b;
        firePropertyChange(ENSURE_SOURCE_CONSISTENCY, old, ensureSourceConsistency);
    }

    public void setParallelProverEnabled(boolean b) {
        var old = parallelProverEnabled;
        parallelProverEnabled = b;
        firePropertyChange(PARALLEL_PROVER_ENABLED, old, parallelProverEnabled);
    }

    public void setParallelProverThreadCount(int count) {
        var old = parallelProverThreadCount;
        parallelProverThreadCount = Math.max(1, count);
        firePropertyChange(PARALLEL_PROVER_THREADS, old, parallelProverThreadCount);
    }

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    public void readSettings(Properties props) {
        var prefix = "[" + CATEGORY + "]";
        String val = props.getProperty(prefix + TACLET_FILTER);
        if (val != null) {
            setTacletFilter(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + DND_DIRECTION_SENSITIVE_KEY);
        if (val != null) {
            dndDirectionSensitive = Boolean.parseBoolean(val);
        }

        val = props.getProperty(prefix + RIGHT_CLICK_MACROS_KEY);
        if (val != null) {
            setRightClickMacros(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + USE_JML_KEY);
        if (val != null) {
            setUseJML(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + AUTO_SAVE);
        if (val != null) {
            try {
                setAutoSave(Integer.parseInt(val));
                if (autoSave < 0) {
                    setAutoSave(0);
                }
            } catch (NumberFormatException e) {
                setAutoSave(0);
            }
        }

        val = props.getProperty(prefix + ENSURE_SOURCE_CONSISTENCY);
        if (val != null) {
            setEnsureSourceConsistency(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + PARALLEL_PROVER_ENABLED);
        if (val != null) {
            setParallelProverEnabled(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + PARALLEL_PROVER_THREADS);
        if (val != null) {
            try {
                setParallelProverThreadCount(Integer.parseInt(val));
            } catch (NumberFormatException e) {
                setParallelProverThreadCount(PARALLEL_PROVER_THREADS_DEFAULT);
            }
        }

        {
            String sysProp = System.getProperty(KEY_JML_ENABLED_KEYS);
            if (sysProp != null) {
                val = sysProp;
                LOGGER.warn("Use system property -P{}={}", KEY_JML_ENABLED_KEYS, sysProp);
            } else {
                val = props.getProperty(prefix + KEY_JML_ENABLED_KEYS);
            }

            if (val != null) {
                setJmlEnabledKeys(new TreeSet<>(Arrays.stream(val.split(",")).toList()));
            }
        }
    }

    /**
     * implements the method required by the Settings interface. The settings are written to the
     * given Properties object. Only entries of the form
     * <key> = <value> (,<value>)* are allowed.
     *
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    @Override
    public void writeSettings(Properties props) {
        var prefix = "[" + CATEGORY + "]";
        props.setProperty(prefix + TACLET_FILTER, String.valueOf(tacletFilter));
        props.setProperty(prefix + DND_DIRECTION_SENSITIVE_KEY,
            String.valueOf(dndDirectionSensitive));
        props.setProperty(prefix + RIGHT_CLICK_MACROS_KEY, String.valueOf(rightClickMacros));
        props.setProperty(prefix + USE_JML_KEY, String.valueOf(useJML));
        props.setProperty(prefix + AUTO_SAVE, String.valueOf(autoSave));
        props.setProperty(prefix + ENSURE_SOURCE_CONSISTENCY,
            String.valueOf(ensureSourceConsistency));
        props.setProperty(prefix + PARALLEL_PROVER_ENABLED, String.valueOf(parallelProverEnabled));
        props.setProperty(prefix + PARALLEL_PROVER_THREADS,
            String.valueOf(parallelProverThreadCount));
        props.setProperty(KEY_JML_ENABLED_KEYS, String.join(",", jmlEnabledKeys));
    }

    @Override
    public void readSettings(Configuration props) {
        setTacletFilter(props.getBool(TACLET_FILTER));
        setDnDDirectionSensitivity(props.getBool(DND_DIRECTION_SENSITIVE_KEY));
        setRightClickMacros(props.getBool(RIGHT_CLICK_MACROS_KEY));
        setUseJML(props.getBool(USE_JML_KEY));
        try {
            var autoSave = props.getInt(AUTO_SAVE);
            setAutoSave(autoSave);
            if (autoSave < 0)
                setAutoSave(0);
        } catch (NumberFormatException e) {
            setAutoSave(0);
        }
        setEnsureSourceConsistency(props.getBool(ENSURE_SOURCE_CONSISTENCY));
        setParallelProverEnabled(props.getBool(PARALLEL_PROVER_ENABLED, false));
        setParallelProverThreadCount(
            props.getInt(PARALLEL_PROVER_THREADS, PARALLEL_PROVER_THREADS_DEFAULT));

        var sysProp = System.getProperty(KEY_JML_ENABLED_KEYS);
        if (sysProp != null) {
            LOGGER.warn("Use system property -P{}={}", KEY_JML_ENABLED_KEYS, sysProp);
            setJmlEnabledKeys(new TreeSet<>(Arrays.stream(sysProp.split(",")).toList()));
        } else {
            setJmlEnabledKeys(new TreeSet<>(props.getStringList(KEY_JML_ENABLED_KEYS)));
        }
    }

    @Override
    public void writeSettings(Configuration props) {
        props.set(TACLET_FILTER, tacletFilter);
        props.set(DND_DIRECTION_SENSITIVE_KEY, dndDirectionSensitive);
        props.set(RIGHT_CLICK_MACROS_KEY, rightClickMacros);
        props.set(USE_JML_KEY, useJML);
        props.set(AUTO_SAVE, autoSave);
        props.set(ENSURE_SOURCE_CONSISTENCY, ensureSourceConsistency);
        props.set(PARALLEL_PROVER_ENABLED, parallelProverEnabled);
        props.set(PARALLEL_PROVER_THREADS, parallelProverThreadCount);
        props.set(KEY_JML_ENABLED_KEYS, jmlEnabledKeys.stream().toList());
    }
}
