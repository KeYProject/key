package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.control.ProofControl;
import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import javax.swing.*;
import javax.xml.bind.annotation.*;
import java.awt.*;
import java.io.Serializable;
import java.util.Date;

/**
 * @author weigl
 */

@XmlTransient
@XmlAccessorType(XmlAccessType.FIELD)
public abstract class Interaction implements Serializable {
    @XmlTransient
    protected InteractionGraphicStyle graphicalStyle = new InteractionGraphicStyle();

    @XmlAttribute
    private Date created = new Date();

    @XmlAttribute
    private boolean favoured = false;

    public Date getCreated() {
        return created;
    }

    public void setCreated(Date created) {
        this.created = created;
    }

    public boolean isFavoured() {
        return favoured;
    }

    public void setFavoured(boolean favoured) {
        this.favoured = favoured;
    }

    public InteractionGraphicStyle getGraphicalStyle() {
        return graphicalStyle;
    }

    public abstract <T> T accept(InteractionVisitor<T> visitor);

    public static class InteractionGraphicStyle {
        private Icon icon;
        private Color backgroundColor, foregroundColor;

        public Icon getIcon() {
            return icon;
        }

        public void setIcon(Icon icon) {
            this.icon = icon;
        }

        public Color getBackgroundColor() {
            return backgroundColor;
        }

        public void setBackgroundColor(Color backgroundColor) {
            this.backgroundColor = backgroundColor;
        }

        public Color getForegroundColor() {
            return foregroundColor;
        }

        public void setForegroundColor(Color foregroundColor) {
            this.foregroundColor = foregroundColor;
        }
    }
}
