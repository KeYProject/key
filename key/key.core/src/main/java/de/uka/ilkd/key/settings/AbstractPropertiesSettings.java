package de.uka.ilkd.key.settings;

import java.util.EventObject;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

/**
 * A base class for own settings based on properties.
 *
 * @author weigl
 */
public abstract class AbstractPropertiesSettings implements Settings {
    private List<SettingsListener> listenerList = new LinkedList<>();
    protected Properties properties;

    public boolean isInitialized() {
        return properties != null;
    }

    @Override
    public void readSettings(Properties props) {
        properties = props;
    }

    @Override
    public void writeSettings(Properties props) {
        props.putAll(properties);
    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    protected void fireSettingsChange() {
        for (SettingsListener listener : listenerList) {
            listener.settingsChanged(new EventObject(this));
        }
    }

}
