package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;
import java.awt.*;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Properties;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class SettingChangeInteraction extends Interaction {
    @XmlAttribute
    private String message;

    private Properties savedSettings;

    @XmlAttribute
    private InteractionListener.SettingType type;

    public SettingChangeInteraction() {
        graphicalStyle.setBackgroundColor(Color.WHITE);
        graphicalStyle.setForegroundColor(Color.gray);
    }

    public SettingChangeInteraction(Properties settings, InteractionListener.SettingType t) {
        this();
        savedSettings = settings;
        type = t;
    }

    @Override
    public String toString() {
        return (message != null ? message + " : " : "") + type;
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
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public InteractionListener.SettingType getType() {
        return type;
    }
}
