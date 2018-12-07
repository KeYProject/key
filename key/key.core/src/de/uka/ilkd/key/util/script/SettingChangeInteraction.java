package de.uka.ilkd.key.util.script;

import java.io.IOException;
import java.io.StringWriter;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */
public class SettingChangeInteraction extends Interaction {
    private String message;
    private Properties savedSettings;
    private SettingType type;

    public SettingChangeInteraction() {
    }

    public SettingChangeInteraction(Properties settings, SettingType t) {
        savedSettings = settings;
        type = t;
    }

    @Override
    public String toString() {
        return message + " : " + type;
    }

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

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        StringWriter writer = new StringWriter();
        try {
            savedSettings.store(writer,null);
        } catch (IOException e) {
            e.printStackTrace();
        }

        sb
            .append("------\n")
            .append("## SettingChangeInteraction ")
            .append(type.name())
            .append("\n")
            .append("### message\n")
            .append(message)
            .append("### savedSettings: \n")
            .append(writer)
            .append("\n\n");

        return sb.toString();
    }

    enum SettingType {
        SMT, CHOICE, STRATEGY
    }
}
