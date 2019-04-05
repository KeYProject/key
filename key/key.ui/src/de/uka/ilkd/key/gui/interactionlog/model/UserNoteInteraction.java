package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;

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

    @Override
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
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

}
