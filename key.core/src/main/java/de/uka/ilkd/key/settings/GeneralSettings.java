// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.settings;

import java.util.EventObject;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.proof.io.AutoSaver;


public class GeneralSettings implements Settings, Cloneable {
    /**
     * This parameter disables the possibility to prune in closed branches. It is meant as a
     * fallback solution if storing all closed goals needs too much memory or is not needed.
     * Pruning is disabled as a default (for command-line mode, tests, ...) and explicitly has
     * to be enabled for interactive mode.
     */
    public static boolean noPruningClosed = true;

    /**
     * If this option is set, the (Disk)FileRepo does not delete its temporary directories
     * (can be used for debugging).
     */
    public static boolean keepFileRepos = false;

    /**
     * if true then JML specifications are globally disabled
     * in this run of KeY, regardless of the regular settings
     */
    public static boolean disableSpecs = false;
    private static final String TACLET_FILTER = "[General]StupidMode";
    private static final String DND_DIRECTION_SENSITIVE_KEY
        = "[General]DnDDirectionSensitive";
    private static final String USE_JML_KEY = "[General]UseJML";
    private static final String RIGHT_CLICK_MACROS_KEY = "[General]RightClickMacros";
    private static final String AUTO_SAVE = "[General]AutoSavePeriod";

    /** The key for storing the ensureSourceConsistency flag in settings */
    private static final String ENSURE_SOURCE_CONSISTENCY = "[General]EnsureSourceConsistency";

    /** minimize interaction is on by default */
    private boolean tacletFilter = true;

    /** is drag and drop instantiation direction sensitive */
    private boolean dndDirectionSensitive = true;

    /** launches the rightclick the macro menu. on by default. */
    private boolean rightClickMacros = true;

    /** JML is active by default */
    private boolean useJML = true;

    /** auto save is disabled by default.
     * Positive values indicate save period.
     */
    private int autoSave = 0;

    /**
     * If enabled, source files are cached at first use to ensure consistency between proof
     * and source code. Toggles between SimpleFilerepo (false) and DiskFileRepo (true).
     */
    private boolean ensureSourceConsistency = true;

    private LinkedList<SettingsListener> listenerList = 
        new LinkedList<SettingsListener>();

    GeneralSettings() {
        addSettingsListener(AutoSaver.settingsListener);
    }

    // getter
    public boolean tacletFilter() {
        return tacletFilter;
    }

    public boolean isDndDirectionSensitive() {        
        return dndDirectionSensitive;
    }

    public boolean isRightClickMacro() {
        return rightClickMacros;
    }

    public boolean useJML() {
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
        if (tacletFilter != b) {
          tacletFilter = b;
          fireSettingsChanged();
        }
    }
    
    public void setDnDDirectionSensitivity(boolean b) {
        if (dndDirectionSensitive != b) {
          dndDirectionSensitive = b;
          fireSettingsChanged();
        }
    }

    public void setRightClickMacros(boolean b) {
        if(this.rightClickMacros != b) {
            rightClickMacros = b;
            fireSettingsChanged();
        }
    }

    public void setUseJML(boolean b) {
        if (useJML != b) {
            useJML = b;
          fireSettingsChanged();
        }
    }

    public void setAutoSave(int period) {
        autoSave = period;
        fireSettingsChanged();
    }

    /**
     * Sets the ensureSourceConsistency flag. This enables/disables caching of source files at first
     * use via a FileRepo.
     * @param b the new truth value of the flag
     */
    public void setEnsureSourceConsistency(boolean b) {
        if (ensureSourceConsistency != b) {
            ensureSourceConsistency = b;
            fireSettingsChanged();
        }
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
        String val = props.getProperty(TACLET_FILTER);
        if (val != null) {
            tacletFilter = Boolean.valueOf(val).booleanValue();
        }

        val = props.getProperty(DND_DIRECTION_SENSITIVE_KEY);
        if (val != null) {
            dndDirectionSensitive = Boolean.valueOf(val).booleanValue();
        }

        val = props.getProperty(RIGHT_CLICK_MACROS_KEY);
        if (val != null) {
            rightClickMacros = Boolean.valueOf(val).booleanValue();
        }

        val = props.getProperty(USE_JML_KEY);
        if (val != null) {
            useJML = Boolean.valueOf(val).booleanValue();
        }

        val = props.getProperty(AUTO_SAVE);
        if (val != null) {
            try {
                autoSave = Integer.parseInt(val);
                if (autoSave < 0) autoSave = 0;
            } catch (NumberFormatException e) {
                autoSave = 0;
            }
        }

        val = props.getProperty(ENSURE_SOURCE_CONSISTENCY);
        if (val != null) {
            ensureSourceConsistency = Boolean.valueOf(val).booleanValue();
        }
    }

    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	props.setProperty(TACLET_FILTER, "" + tacletFilter);
        props.setProperty(DND_DIRECTION_SENSITIVE_KEY, "" + dndDirectionSensitive);
        props.setProperty(RIGHT_CLICK_MACROS_KEY, "" + rightClickMacros);
        props.setProperty(USE_JML_KEY, "" + useJML);
        props.setProperty(AUTO_SAVE, ""+ autoSave);
        props.setProperty(ENSURE_SOURCE_CONSISTENCY, "" + ensureSourceConsistency);
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new EventObject(this));
        }
    }

    /** 
     * adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    /**
     * removes the listener from the settings object
     * @param l the listener to remove
     */
    public void removeSettingsListener(SettingsListener l) {
        listenerList.remove(l);
    }
}
