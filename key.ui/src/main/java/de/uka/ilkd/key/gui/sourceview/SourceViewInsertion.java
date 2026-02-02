package de.uka.ilkd.key.gui.sourceview;

import javax.swing.text.AttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

public class SourceViewInsertion {

    public final String Group;

    public final int Line; // in Source

    public final String Text; // Inserted Text, can contain linebreaks, tabs, etc

    public final Color Foreground; // Text foreground color
    public final Color Background; // Text background color
    public final Color LineColor;  // Background color of whole line

    public Color OverrideForeground; // Temporary overwrite (e.g. for hover)
    public Color OverrideBackground; // Temporary overwrite (e.g. for hover)

    private SimpleAttributeSet attr = null;

    private final List<ClickListener> clickListener = new LinkedList<>();
    private final List<ClickListener> rightClickListener = new LinkedList<>();
    private final List<MouseMotionListener> mouseEnterListener = new LinkedList<>();
    private final List<MouseMotionListener> mouseLeaveListener = new LinkedList<>();
    private final List<MouseMotionListener> mouseMoveListener = new LinkedList<>();

    public SourceViewInsertion(String group, int line, String text, Color fg, Color bg, Color ln) {
        Group = group;
        Line = line;
        Text = text;
        Foreground = fg;
        Background = bg;
        LineColor = ln;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        SourceViewInsertion that = (SourceViewInsertion) o;
        return Line == that.Line && Group.equals(that.Group) && Text.equals(that.Text);
    }

    @Override
    public int hashCode() {
        return Objects.hash(Group, Line, Text);
    }

    public String getCleanText() {
        return Text.replaceAll("[\r\n]", "").replaceAll("\t", "    ");
    }

    public AttributeSet getStyleAttrbuteSet() {
        if (attr != null) {
            return attr;
        }

        attr = new SimpleAttributeSet();

        if (OverrideForeground != null) {
            StyleConstants.setForeground(attr, OverrideForeground);
        } else if (Foreground != null) {
            StyleConstants.setForeground(attr, Foreground);
        }

        if (OverrideBackground != null) {
            StyleConstants.setBackground(attr, OverrideBackground);
        } else if (Background != null) {
            StyleConstants.setBackground(attr, Background);
        }

        return attr;
    }

    public void addClickListener(ClickListener l) {
        this.clickListener.add(l);
    }

    public void addRightClickListener(ClickListener l) {
        this.rightClickListener.add(l);
    }

    public void addMouseEnterListener(MouseMotionListener l) {
        this.mouseEnterListener.add(l);
    }

    public void addMouseLeaveListener(MouseMotionListener l) {
        this.mouseLeaveListener.add(l);
    }

    public void addMouseMoveListener(MouseMotionListener l) {
        this.mouseMoveListener.add(l);
    }

    public void triggerClickListener(MouseEvent e) {
        for (ClickListener l : this.clickListener) {
            l.onClick(e);
        }
    }

    public void triggerRightClickListener(MouseEvent e) {
        for (ClickListener l : this.rightClickListener) {
            l.onClick(e);
        }
    }

    public void triggerMouseEnterListener(MouseEvent e) {
        for (MouseMotionListener l : this.mouseEnterListener) {
            l.onMotion(e);
        }
    }

    public void triggerMouseLeaveListener(MouseEvent e) {
        for (MouseMotionListener l : this.mouseLeaveListener) {
            l.onMotion(e);
        }
    }

    public void triggerMouseMoveListener(MouseEvent e) {
        for (MouseMotionListener l : this.mouseMoveListener) {
            l.onMotion(e);
        }
    }

    public boolean hasClickListener() {
        return this.clickListener.size() > 0;
    }

    public void setForegroundOverride(Color c) {
        OverrideForeground = c;
        attr = null;
    }

    public void clearForegroundOverride() {
        OverrideForeground = null;
        attr = null;
    }

    public void setBackgroundOverride(Color c) {
        OverrideBackground = c;
        attr = null;
    }

    public void clearBackgroundOverride() {
        OverrideBackground = null;
        attr = null;
    }

    public interface ClickListener {
        void onClick(MouseEvent e);
    }

    public interface MouseMotionListener {
        void onMotion(MouseEvent e);
    }
}
