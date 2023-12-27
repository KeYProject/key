/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.settings.FeatureSettings.createFeature;


public class GeneralSettings extends AbstractSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(GeneralSettings.class);
    private static final String CATEGORY = "General";

    private static final String KEY_TACLET_FILTER = "StupidMode";
    private static final String KEY_DND_DIRECTION_SENSITIVE = "DnDDirectionSensitive";
    private static final String KEY_USE_JML = "UseJML";

    private static final String KEY_JML_ENABLED_KEYS = "JML_ENABLED_KEYS";

    private static final String KEY_RIGHT_CLICK_MACROS_KEY = "RightClickMacros";
    private static final String KEY_AUTO_SAVE = "AutoSavePeriod";

    public static final FeatureSettings.Feature FEATURE_JML_ENTITY_NAMES_AS_TERMLABEL =
        createFeature("JML_ENTITY_NAMES_AS_TERMLABEL", "Translates the names for JML entities " +
            "as term labels on the sequents.");

    /**
     * The key for storing the ensureSourceConsistency flag in settings
     */
    private static final String KEY_ENSURE_SOURCE_CONSISTENCY = "EnsureSourceConsistency";


    /**
     * This parameter disables the possibility to prune in closed branches. It is meant as a
     * fallback solution if storing all closed goals needs too much memory or is not needed. Pruning
     * is disabled as a default (for command-line mode, tests, ...) and explicitly has to be enabled
     * for interactive mode.
     */
    private boolean noPruningClosed = true;

    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary directories (can be
     * used for debugging).
     */
    private boolean keepFileRepos = false;

    /**
     * if true then JML specifications are globally disabled in this run of KeY, regardless of the
     * regular settings
     */
    private boolean disableSpecs = false;


    /**
     * Enabled keys for the evaluation of JML conditional annotation texts
     */
    private Set<String> jmlEnabledKeys = new TreeSet<>(Set.of("key"));

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

    // setter
    public void setTacletFilter(boolean b) {
        var old = tacletFilter;
        tacletFilter = b;
        firePropertyChange(KEY_TACLET_FILTER, old, b);
    }

    public void setDnDDirectionSensitivity(boolean b) {
        var old = dndDirectionSensitive;
        dndDirectionSensitive = b;
        firePropertyChange(KEY_DND_DIRECTION_SENSITIVE, old, dndDirectionSensitive);
    }

    public void setRightClickMacros(boolean b) {
        var old = rightClickMacros;
        rightClickMacros = b;
        firePropertyChange(KEY_RIGHT_CLICK_MACROS_KEY, old, rightClickMacros);
    }

    public void setUseJML(boolean b) {
        var old = useJML;
        useJML = b;
        firePropertyChange(KEY_USE_JML, old, useJML);
    }

    public void setAutoSave(int period) {
        var old = autoSave;
        autoSave = period;
        firePropertyChange(KEY_AUTO_SAVE, old, autoSave);
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
        firePropertyChange(KEY_ENSURE_SOURCE_CONSISTENCY, old, ensureSourceConsistency);
    }

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    public void readSettings(Properties props) {
        var prefix = "[" + CATEGORY + "]";
        String val = props.getProperty(prefix + KEY_TACLET_FILTER);
        if (val != null) {
            setTacletFilter(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + KEY_DND_DIRECTION_SENSITIVE);
        if (val != null) {
            dndDirectionSensitive = Boolean.parseBoolean(val);
        }

        val = props.getProperty(prefix + KEY_RIGHT_CLICK_MACROS_KEY);
        if (val != null) {
            setRightClickMacros(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + KEY_USE_JML);
        if (val != null) {
            setUseJML(Boolean.parseBoolean(val));
        }

        val = props.getProperty(prefix + KEY_AUTO_SAVE);
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

        val = props.getProperty(prefix + KEY_ENSURE_SOURCE_CONSISTENCY);
        if (val != null) {
            setEnsureSourceConsistency(Boolean.parseBoolean(val));
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
        props.setProperty(prefix + KEY_TACLET_FILTER, String.valueOf(tacletFilter));
        props.setProperty(prefix + KEY_DND_DIRECTION_SENSITIVE,
            String.valueOf(dndDirectionSensitive));
        props.setProperty(prefix + KEY_RIGHT_CLICK_MACROS_KEY, String.valueOf(rightClickMacros));
        props.setProperty(prefix + KEY_USE_JML, String.valueOf(useJML));
        props.setProperty(prefix + KEY_AUTO_SAVE, String.valueOf(autoSave));
        props.setProperty(prefix + KEY_ENSURE_SOURCE_CONSISTENCY,
            String.valueOf(ensureSourceConsistency));
        props.setProperty(KEY_JML_ENABLED_KEYS, String.join(",", jmlEnabledKeys));
    }

    @Override
    public void readSettings(Configuration props) {
        setTacletFilter(props.getBool(KEY_TACLET_FILTER));
        setDnDDirectionSensitivity(props.getBool(KEY_DND_DIRECTION_SENSITIVE));
        setRightClickMacros(props.getBool(KEY_RIGHT_CLICK_MACROS_KEY));
        setUseJML(props.getBool(KEY_USE_JML));
        try {
            var autoSave = props.getInt(KEY_AUTO_SAVE);
            setAutoSave(autoSave);
            if (autoSave < 0)
                setAutoSave(0);
        } catch (NumberFormatException e) {
            setAutoSave(0);
        }
        setEnsureSourceConsistency(props.getBool(KEY_ENSURE_SOURCE_CONSISTENCY));

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
        props.set(KEY_TACLET_FILTER, tacletFilter);
        props.set(KEY_DND_DIRECTION_SENSITIVE, dndDirectionSensitive);
        props.set(KEY_RIGHT_CLICK_MACROS_KEY, rightClickMacros);
        props.set(KEY_USE_JML, useJML);
        props.set(KEY_AUTO_SAVE, autoSave);
        props.set(KEY_ENSURE_SOURCE_CONSISTENCY, ensureSourceConsistency);
        props.set(KEY_JML_ENABLED_KEYS, jmlEnabledKeys.stream().toList());
    }

    public void setNoPruningClosed(boolean noPruningClosed) {
        var oldValue = this.noPruningClosed;
        this.noPruningClosed = noPruningClosed;
        firePropertyChange("noPruningClosed", oldValue, noPruningClosed);
    }

    public void setKeepFileRepos(boolean keepFileRepos) {
        var oldValue = this.keepFileRepos;
        this.keepFileRepos = keepFileRepos;
        firePropertyChange("keepFileRepos", oldValue, keepFileRepos);
    }

    public void setDisableSpecs(boolean disableSpecs) {
        var oldValue = this.disableSpecs;
        this.disableSpecs = disableSpecs;
        firePropertyChange(KEY_USE_JML, oldValue, disableSpecs);
    }

    public void setDndDirectionSensitive(boolean dndDirectionSensitive) {
        var oldValue = this.dndDirectionSensitive;
        this.dndDirectionSensitive = dndDirectionSensitive;
        firePropertyChange(KEY_DND_DIRECTION_SENSITIVE, oldValue, dndDirectionSensitive);
    }

    public boolean isNoPruningClosed() {
        return noPruningClosed;
    }

    public boolean isKeepFileRepos() {
        return keepFileRepos;
    }

    public boolean isDisableSpecs() {
        return disableSpecs;
    }

    public boolean isTacletFilter() {
        return tacletFilter;
    }

    public boolean isRightClickMacros() {
        return rightClickMacros;
    }

    public int getAutoSave() {
        return autoSave;
    }
}
