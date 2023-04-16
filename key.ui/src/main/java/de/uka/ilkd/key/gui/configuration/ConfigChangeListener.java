package de.uka.ilkd.key.gui.configuration;

/**
 * The ConfigChangeListener is notified if the UI settings in class Config change.
 */
public interface ConfigChangeListener {

    /** focused node has changed */
    void configChanged(ConfigChangeEvent e);

}
