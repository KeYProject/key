/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.awt.*;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

import org.key_project.ui.interactionlog.api.Interaction;

/**
 * @author Alexander Weigl
 * @version 1 (07.12.18)
 */

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class UserNoteInteraction extends Interaction {
    private static final long serialVersionUID = 1L;

    private String note;

    public UserNoteInteraction() {
        graphicalStyle.setBackgroundColor(Color.red.brighter().brighter().brighter());
        // TODO graphicalStyle.setIcon();
    }

    public UserNoteInteraction(String note) {
        this();
        this.note = note;
    }

    public String getNote() {
        return note;
    }

    public void setNote(String note) {
        this.note = note;
    }

    @Override
    public String toString() {
        return note;
    }

    @Override
    public String getMarkdown() {
        return String.format("## Note%n" +
            "**Date**: %s%n" +
            "```%n%s%n```", getCreated(), getNote());
    }
}
