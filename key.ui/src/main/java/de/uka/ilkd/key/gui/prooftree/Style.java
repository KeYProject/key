package de.uka.ilkd.key.gui.prooftree;

import javax.swing.*;
import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Style {
    /** the text of this node */
    public String text;

    /** the tooltip */
    public Tooltip tooltip;

    /** foreground color of the node */
    public Color foreground;

    /** background color of the node */
    public Color background;

    /** border color of the node */
    public Color border;

    /** icon of the node */
    public Icon icon;

    public static class Tooltip {
        public String title = "";
        public String notes = "";
        public String additionalInfo = "";
    }
}
