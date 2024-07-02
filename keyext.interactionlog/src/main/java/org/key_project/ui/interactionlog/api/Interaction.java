package org.key_project.ui.interactionlog.api;

import org.key_project.ui.interactionlog.api.Markdownable;
import org.key_project.ui.interactionlog.api.Reapplicable;
import org.key_project.ui.interactionlog.api.Scriptable;

import javax.swing.*;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlTransient;
import java.awt.*;
import java.io.Serializable;
import java.util.Date;

/**
 * @author weigl
 */

@XmlTransient
@XmlAccessorType(XmlAccessType.FIELD)
public abstract class Interaction implements Serializable, Markdownable, Scriptable, Reapplicable {
    private static final long serialVersionUID = -7031665632460180825L;

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
