// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.rule.UpdateSimplifier;

/** This class encapsulates the information about the active
 * update simplifier settings
 */
public class SimultaneousUpdateSimplifierSettings implements Settings {


    private static final String DELETE_EFFECTLESS_KEY = 
	"[SimultaneousUpdateSimplifier]DeleteEffectLessLocations";
    private static final String EAGER_MODE_KEY = 
	"[SimultaneousUpdateSimplifier]EagerSimplification";
 
    private boolean delete_effectless_updates = true;
    private boolean eagerMode = false;
 
    private UpdateSimplifier sus;

    private LinkedList listenerList = new LinkedList();

    public SimultaneousUpdateSimplifierSettings() {
	updateSimplifier();
    }
    
    // 
    private void updateSimplifier() {
	sus = new UpdateSimplifier(deleteEffectlessUpdates(), eagerMode());
    }

    // getter
    public boolean deleteEffectlessUpdates() {
	return delete_effectless_updates;
    }

    public boolean eagerMode() {
	return eagerMode;
    }

    // setter

    public void setDeleteEffectlessUpdates(boolean b) {
        if(delete_effectless_updates != b) {
	  delete_effectless_updates = b;
	  fireSettingsChanged();
	}
    }


    public void setEagerMode(boolean b) {
        if (eagerMode != b) {
	  eagerMode = b;
	  fireSettingsChanged();
	}
    }


    // 
    public UpdateSimplifier getSimplifier() {
	return sus;
    }

    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	String deleteEffectlessString = props.getProperty(DELETE_EFFECTLESS_KEY);	
	String eagerModeString = props.getProperty(EAGER_MODE_KEY);	

	if (deleteEffectlessString != null) {
	    delete_effectless_updates = Boolean.valueOf(deleteEffectlessString)
				       .booleanValue();
	}
	if (eagerModeString != null) {
	    eagerMode = Boolean.valueOf(eagerModeString).booleanValue();
	}
	
    }


    /** implements the method required by the Settings interface. The
     * settings are written to the given Properties object. Only entries of the form 
     * <key> = <value> (,<value>)* are allowed.
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    public void writeSettings(Properties props) {
	props.setProperty(DELETE_EFFECTLESS_KEY,   "" + delete_effectless_updates);
	props.setProperty(EAGER_MODE_KEY,   "" + eagerMode);
   }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	updateSimplifier();

	Iterator it = listenerList.iterator();
	while (it.hasNext()) {
	    ((SettingsListener)it.next()).settingsChanged(new GUIEvent(this));
	}
    }

    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }

}
