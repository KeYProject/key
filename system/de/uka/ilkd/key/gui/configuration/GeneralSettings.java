// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.configuration;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.gui.GUIEvent;


/** This class encapsulates the information about the active
 * Heuristics and the maximum amount of heuristics steps before an
 * interactive step is required.
 */
public class GeneralSettings implements Settings {


    private static final String STUPID_MODE_KEY = "[General]StupidMode";
    private static final String PROOF_ASSISTANT_MODE_KEY = "[General]ProofAssistant";

    private static final String SOUND_NOTIFICATION_KEY = "[General]SoundNotification";
    private static final String DND_DIRECTION_SENSITIVE_KEY = 
        "[General]DnDDirectionSensitive";
    private static final String USE_JML_KEY = "[General]UseJML";
    private static final String USE_OCL_KEY = "[General]UseOCL";
    
    /** if true then JML/OCL specifications are globally disabled 
     * in this run of KeY, regardless of the regular settings 
     */
    public static boolean disableSpecs = false;
    
    /** minimize interaction is on by default */
    private boolean stupidMode = true;

    /** proof assistant is on by default */
    private boolean proofAssistantMode = true;

    /** suggestive var names are off by default */
    private boolean suggestiveVarNames = false;

    /** sound notification is on by default */
    private boolean soundNotification = true;

    /** is drag and drop instantiation direction sensitive */
    private boolean dndDirectionSensitive = true;
    
    /** JML is active by default */
    private boolean useJML = true;
    
    /** OCL is not active by default */
    private boolean useOCL = false;

    private LinkedList<SettingsListener> listenerList = 
        new LinkedList<SettingsListener>();


    // getter
    public boolean stupidMode() {
	return stupidMode;
    }

    
    public boolean proofAssistantMode() {
	return proofAssistantMode;
    }

    
    public boolean suggestiveVarNames() {
	return suggestiveVarNames;
    }
    

    public boolean soundNotification() {
        return soundNotification;
    }


    public boolean isDndDirectionSensitive() {        
        return dndDirectionSensitive;
    }
    
    
    public boolean useJML() {
        return useJML && !disableSpecs;
    }
    
    
    public boolean useOCL() {
        return useOCL && !disableSpecs;
    }
    

    // setter
    public void setStupidMode(boolean b) {
        if (stupidMode != b) {
          stupidMode = b;
          fireSettingsChanged();
        }
    }

    
    public void setProofAssistantMode(boolean b) {
        if(proofAssistantMode != b) {
	  proofAssistantMode = b;
	  fireSettingsChanged();
	}
    }
    

    public void setSoundNotification(boolean b) {
        if (soundNotification != b) {
          soundNotification = b;
          fireSettingsChanged();
	}
    }

    
    public void setUseJML(boolean b) {
        if (useJML != b) {
            useJML = b;
          fireSettingsChanged();
        }
    }
    
    
    public void setUseOCL(boolean b) {
        if (useOCL != b) {
            useOCL = b;
          fireSettingsChanged();
        }
    }


    
    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	String val = props.getProperty(STUPID_MODE_KEY);
	if (val != null) {
	    stupidMode = Boolean.valueOf(val).booleanValue();
	}

	val = props.getProperty(PROOF_ASSISTANT_MODE_KEY);
	if (val != null) {
	    proofAssistantMode = Boolean.valueOf(val).booleanValue();
	}
    
	val = props.getProperty(SOUND_NOTIFICATION_KEY);
	if (val != null) {
	    soundNotification = Boolean.valueOf(val).booleanValue();
	} 
        
        val = props.getProperty(DND_DIRECTION_SENSITIVE_KEY);
        if (val != null) {
            dndDirectionSensitive = Boolean.valueOf(val).booleanValue();
        }         
        
        val = props.getProperty(USE_JML_KEY);
        if (val != null) {
            useJML = Boolean.valueOf(val).booleanValue();
        }         
        
        val = props.getProperty(USE_OCL_KEY);
        if (val != null) {
            useOCL = Boolean.valueOf(val).booleanValue();
        }                 
    }


    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	props.setProperty(STUPID_MODE_KEY, "" + stupidMode);
	props.setProperty(PROOF_ASSISTANT_MODE_KEY, "" + proofAssistantMode);
        props.setProperty(SOUND_NOTIFICATION_KEY, "" + soundNotification);
        props.setProperty(DND_DIRECTION_SENSITIVE_KEY, "" + dndDirectionSensitive);
        props.setProperty(USE_JML_KEY, "" + useJML);
        props.setProperty(USE_OCL_KEY, "" + useOCL);
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new GUIEvent(this));
        }
    }

    
    /** 
     * adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }
}
