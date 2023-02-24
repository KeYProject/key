package de.uka.ilkd.key.settings;

import java.util.EventObject;



/**
 * This interface is implemented by objects that listen to settings object. An object implementing
 * the settings interface will call the method settingChanged of the listener
 */
public interface SettingsListener {

    /**
     * called by the Settings object to inform the listener that its state has changed
     *
     * @param e the Event sent to the listener
     */
    void settingsChanged(EventObject e);
}
