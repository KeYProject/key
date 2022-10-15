package de.uka.ilkd.key.gui.sourceview;

import javax.annotation.Nonnull;
import javax.swing.text.AttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import java.awt.*;
import java.util.Objects;

public class SourceViewInsertion {

    public final String Group;

    public final int Line; // in Source

    public final String Text;

    public final Color Foreground;
    public final Color Background;

    private SimpleAttributeSet attr = null;

    //TODO Style, RightClickListener, LeftClickListener, OnMouseEnterListener, OnMouseELeaveListener


    public SourceViewInsertion(String group, int line, String text, Color fg, Color bg) {
        Group = group;
        Line = line;
        Text = text;
        Foreground = fg;
        Background = bg;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SourceViewInsertion that = (SourceViewInsertion) o;
        return Line == that.Line && Group.equals(that.Group) && Text.equals(that.Text);
    }

    @Override
    public int hashCode() {
        return Objects.hash(Group, Line, Text);
    }

    public String getCleanText() {
        return Text.replaceAll("[\r\n]", "");
    }

    public AttributeSet getStyleAttrbuteSet() {
        if (attr != null) {
            return attr;
        }

        attr = new SimpleAttributeSet();
        StyleConstants.setForeground(attr, Foreground);
        StyleConstants.setBackground(attr, Background);

        return attr;
    }
}
