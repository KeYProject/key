package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;

import javax.swing.*;
import java.awt.*;
import java.io.Serializable;
import java.util.Date;

/**
 * @author weigl
 */
public abstract class Interaction implements Serializable {
    protected InteractionGraphicStyle graphicalStyle = new InteractionGraphicStyle();
    private Date created = new Date();
    private boolean favoured = false;

    public String getProofScriptRepresentation(Services services) {
        throw new UnsupportedOperationException();
    }

    public abstract String getMarkdownText();

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
