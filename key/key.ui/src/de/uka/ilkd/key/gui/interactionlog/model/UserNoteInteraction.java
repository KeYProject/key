package de.uka.ilkd.key.gui.interactionlog.model;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (07.12.18)
 */

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class UserNoteInteraction extends Interaction {
    private String note;

    public UserNoteInteraction() {
        graphicalStyle.setBackgroundColor(Color.red.brighter().brighter().brighter());
        //TODO graphicalStyle.setIcon();
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
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder();

        sb
                .append("------\n")
                .append("## UserNoteInteraction ")
                .append("\n")
                .append("### Content:\n")
                .append("```\n")
                .append(note)
                .append("\n```")
                .append("\n\n");

        return sb.toString();
    }
}
