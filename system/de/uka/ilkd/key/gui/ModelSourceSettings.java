// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.gui.configuration.Settings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;

public class ModelSourceSettings implements Settings{

    private static final String MODEL_SOURCE_KEY = "[Model]Source";

    private LinkedList<SettingsListener> listenerList = new LinkedList<SettingsListener>();
    private String modelSource="1";
    private String modelSourceNew;
    private boolean changed;
    
    public ModelSourceSettings() {
	restore();
    }
        
    public String getModelSource(){
	return modelSource;
    }
     
    /** restores old values */
    public void restore() {
	modelSourceNew=modelSource;
    }

    public void store() {
	modelSource=modelSourceNew;
	fireSettingsChanged();
    }

  
    public void setModelSource(String value) {
	modelSourceNew = value;
    }
    
    /** gets a Properties object and has to perform the necessary
     * steps in order to change this object in a way that it
     * represents the stored settings
     */
    public void readSettings(Properties props) {
	String source = props.getProperty(MODEL_SOURCE_KEY);
	if (source == null)
	    modelSource="1";
	else
	    modelSource=source;
	restore();
    }

    public void writeSettings(Properties props) {
	props.setProperty(MODEL_SOURCE_KEY, modelSourceNew);
    }

    public void setChanged(boolean arg){
	changed=arg;
    }

    /** sends the message that the state of this setting has been
     * changed to its registered listeners (not thread-safe)
     */
    protected void fireSettingsChanged() {
	Iterator<SettingsListener> it = listenerList.iterator();
	while (it.hasNext()) {
	    it.next().settingsChanged(new GUIEvent(this));
	}
    }

    /** adds a listener to the settings object 
     * @param l the listener
     */
    public void addSettingsListener(SettingsListener l) {
	listenerList.add(l);
    }



}
