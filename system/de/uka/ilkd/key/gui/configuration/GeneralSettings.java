// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
    private static final String SUGG_VARNAMES_KEY = "[General]SuggestiveVarNames";
    private static final String OUTER_RENAMING_KEY = "[General]OuterRenaming";

    private static final String SOUND_NOTIFICATION_KEY = "[General]SoundNotification";
    private static final String DND_DIRECTION_SENSITIVE_KEY = 
        "[General]DnDDirectionSensitive";
    
    /** minimize interaction is on by default */
    private boolean stupidMode = true;

    /** proof assistant is on by default */
    private boolean proofAssistantMode = true;

    /** suggestive var names are off by default */
    private boolean suggestiveVarNames = false;

    /** outer renaming is on by default */
    private boolean outerRenaming = false;

    /** sound notification is on by default */
    private boolean soundNotification = true;

    /** is drag and drop instantiation direction sensitive */
    private boolean dndDirectionSensitive = true;

    private LinkedList listenerList = new LinkedList();


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
    
    public boolean outerRenaming() {
    	return outerRenaming;
    }

    public boolean soundNotification() {
        return soundNotification;
    }

    /**
     * returns true if drag and drop shall be direction sensitive   
     */
    public boolean isDndDirectionSensitive() {        
        return dndDirectionSensitive;
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
    
    public void setSuggestiveVarNames(boolean b) {
        if(suggestiveVarNames != b) {
	  suggestiveVarNames = b;
	  fireSettingsChanged();
	}
    }
    
    public void setOuterRenaming(boolean b) {
        if (outerRenaming != b) {
    	  outerRenaming = b;
	  fireSettingsChanged();
	}
    }

    public void setSoundNotification(boolean b) {
        if (soundNotification != b) {
          soundNotification = b;
          fireSettingsChanged();
	}
    }

    public void setDnDDirectionSensitivity(boolean b) {
        if (dndDirectionSensitive != b) {
          dndDirectionSensitive = b;
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

	val = props.getProperty(SUGG_VARNAMES_KEY);
	if (val != null) {
	    suggestiveVarNames = Boolean.valueOf(val).booleanValue();
	} 

	val = props.getProperty(OUTER_RENAMING_KEY);
	if (val != null) {
	    outerRenaming = Boolean.valueOf(val).booleanValue();
	} 
    
	val = props.getProperty(SOUND_NOTIFICATION_KEY);
	if (val != null) {
	    soundNotification = Boolean.valueOf(val).booleanValue();
	} 
        
        val = props.getProperty(DND_DIRECTION_SENSITIVE_KEY);
        if (val != null) {
            dndDirectionSensitive = Boolean.valueOf(val).booleanValue();
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
	props.setProperty(SUGG_VARNAMES_KEY, "" + suggestiveVarNames);
	props.setProperty(OUTER_RENAMING_KEY, "" + outerRenaming);
        props.setProperty(SOUND_NOTIFICATION_KEY, "" + soundNotification);
        props.setProperty(DND_DIRECTION_SENSITIVE_KEY, "" + dndDirectionSensitive);
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	Iterator it = listenerList.iterator();
	while (it.hasNext()) {
	    ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
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
