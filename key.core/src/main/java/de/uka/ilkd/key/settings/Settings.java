package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.util.Properties;

/**
 * This interface is implemented by classes that are used to store settings for different proposes
 * (like active heuristics, which LDTs to use etc.)
 */
public interface Settings {

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    void readSettings(Properties props);

    /**
     * The settings to store are written to the given Properties object.
     *
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    void writeSettings(Properties props);

    /**
     * gets a Properties object and has to perform the necessary steps in order to change this
     * object in a way that it represents the stored settings
     */
    void readSettings(Configuration props);

    /**
     * The settings to store are written to the given Properties object.
     *
     * @param props the Properties object where to write the settings as (key, value) pair
     */
    void writeSettings(Configuration props);


    void addPropertyChangeListener(PropertyChangeListener listener);

    void removePropertyChangeListener(PropertyChangeListener listener);

    PropertyChangeListener[] getPropertyChangeListeners();

    void addPropertyChangeListener(String propertyName, PropertyChangeListener listener);

    void removePropertyChangeListener(String propertyName, PropertyChangeListener listener);
}
