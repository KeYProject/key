package de.uka.ilkd.key.util.script;

import java.util.Date;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class SettingChangeInteraction implements Interaction {
    private String message;
    private Properties savedSettings;
    private SettingType type;
    private Date created = new Date();

    public SettingChangeInteraction(Properties settings, SettingType t) {
        savedSettings = settings;
        type = t;
    }


    @Override
    public Date created() { return created; }

    public String getMessage() {
        return message;
    }

    public void setMessage(String message) {
        this.message = message;
    }

    public Properties getSavedSettings() {
        return savedSettings;
    }

    public void setSavedSettings(Properties savedSettings) {
        this.savedSettings = savedSettings;
    }

    enum SettingType {
        SMT, CHOICE, STRATEGY
    }
}
