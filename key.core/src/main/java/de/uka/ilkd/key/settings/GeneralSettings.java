/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.Properties;


public class GeneralSettings extends AbstractSettings {
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


    private static final String TACLET_FILTER = "[General]StupidMode";
    private static final String DND_DIRECTION_SENSITIVE_KEY = "[General]DnDDirectionSensitive";
    private static final String USE_JML_KEY = "[General]UseJML";
    private static final String RIGHT_CLICK_MACROS_KEY = "[General]RightClickMacros";
    private static final String AUTO_SAVE = "[General]AutoSavePeriod";

    /**
     * The key for storing the ensureSourceConsistency flag in settings
     */
    private static final String ENSURE_SOURCE_CONSISTENCY = "[General]EnsureSourceConsistency";

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

    // getter
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

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    public void readSettings(Properties props) {
        String val = props.getProperty(TACLET_FILTER);
        if (val != null) {
            setTacletFilter(Boolean.parseBoolean(val));
        }

        val = props.getProperty(DND_DIRECTION_SENSITIVE_KEY);
        if (val != null) {
            dndDirectionSensitive = Boolean.parseBoolean(val);
        }

        val = props.getProperty(RIGHT_CLICK_MACROS_KEY);
        if (val != null) {
            setRightClickMacros(Boolean.parseBoolean(val));
        }

        val = props.getProperty(USE_JML_KEY);
        if (val != null) {
            setUseJML(Boolean.parseBoolean(val));
        }

        val = props.getProperty(AUTO_SAVE);
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

        val = props.getProperty(ENSURE_SOURCE_CONSISTENCY);
        if (val != null) {
            setEnsureSourceConsistency(Boolean.parseBoolean(val));
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
        props.setProperty(TACLET_FILTER, String.valueOf(tacletFilter));
        props.setProperty(DND_DIRECTION_SENSITIVE_KEY, String.valueOf(dndDirectionSensitive));
        props.setProperty(RIGHT_CLICK_MACROS_KEY, String.valueOf(rightClickMacros));
        props.setProperty(USE_JML_KEY, String.valueOf(useJML));
        props.setProperty(AUTO_SAVE, String.valueOf(autoSave));
        props.setProperty(ENSURE_SOURCE_CONSISTENCY, String.valueOf(ensureSourceConsistency));
    }
}
