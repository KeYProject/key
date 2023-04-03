package de.uka.ilkd.key.settings;

import java.util.EventObject;
import java.util.LinkedList;
import java.util.Properties;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Proof-dependent settings for {@link TermLabel}s.
 *
 * @author lanzinger
 */
public class TermLabelSettings implements Settings, Cloneable {
    private static final Logger LOGGER = LoggerFactory.getLogger(TermLabelSettings.class);

    /**
     * Property key for {@link #getUseOriginLabels()}
     */
    private static final String USE_ORIGIN_LABELS = "[Labels]UseOriginLabels";

    /**
     * @see {@link #getUseOriginLabels()}
     */
    private boolean useOriginLabels = true;

    /**
     * @see #addSettingsListener(SettingsListener)
     * @see #removeSettingsListener(SettingsListener)
     */
    private final LinkedList<SettingsListener> listenerList = new LinkedList<>();

    @Override
    public void readSettings(Properties props) {
        String str = props.getProperty(USE_ORIGIN_LABELS);

        if (str != null && (str.equals("true") || str.equals("false"))) {
            setUseOriginLabels(Boolean.parseBoolean(str));
        } else {
            LOGGER.debug("TermLabelSettings: Failure while reading the setting \"UseOriginLabels\"."
                + "Using the default value: true." + "The string read was: {}", str);
            setUseOriginLabels(true);
        }
    }

    @Override
    public void writeSettings(Properties props) {
        props.setProperty(USE_ORIGIN_LABELS, Boolean.toString(useOriginLabels));
    }

    /**
     *
     * @return {@code true} iff {@link OriginTermLabel}s should be used.
     */
    public boolean getUseOriginLabels() {
        return useOriginLabels;
    }

    /**
     * Sets the value returned by {@link #getUseOriginLabels()}
     *
     * @param useOriginLabels whether {@link OriginTermLabel}s should be used.
     */
    public void setUseOriginLabels(boolean useOriginLabels) {
        if (this.useOriginLabels != useOriginLabels) {
            this.useOriginLabels = useOriginLabels;
            fireSettingsChanged();
        }
    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listenerList.add(l);
    }

    /**
     * Removes a listener from this settings object.
     *
     * @param l the listener to remove.
     */
    public void removeSettingsListener(SettingsListener l) {
        listenerList.remove(l);
    }

    /**
     * Notify all listeners of the current state of this settings object.
     */
    protected void fireSettingsChanged() {
        for (SettingsListener aListenerList : listenerList) {
            aListenerList.settingsChanged(new EventObject(this));
        }
    }
}
