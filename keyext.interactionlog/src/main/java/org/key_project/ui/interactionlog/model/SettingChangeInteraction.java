/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.awt.*;
import java.io.IOException;
import java.io.StringWriter;
import java.util.Properties;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.ui.interactionlog.api.Interaction;

/**
 * @author Alexander Weigl
 * @version 1 (06.12.18)
 */

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class SettingChangeInteraction extends Interaction {
    private static final long serialVersionUID = 1L;

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

    public InteractionListener.SettingType getType() {
        return type;
    }

    @Override
    public String getMarkdown() {
        StringWriter writer = new StringWriter();
        try {
            getSavedSettings().store(writer, "");
        } catch (IOException e) {
            e.printStackTrace();
        }
        return String.format("Setting changed: %s%n%n```%n%s%n````%n", getType().name(), writer);
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        ProofSettings settings = goal.proof().getSettings();
        switch (getType()) {
        case SMT:
            settings.getSMTSettings().readSettings(getSavedSettings());
            break;
        case CHOICE:
            settings.getChoiceSettings().readSettings(getSavedSettings());
            break;
        case STRATEGY:
            settings.getStrategySettings().readSettings(getSavedSettings());
            break;
        }
    }
}
