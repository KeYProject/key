package de.uka.ilkd.key.gui.sourceview;

import javax.annotation.Nonnull;
import java.util.Objects;

public class SourceViewInsertion {

    public final String Group;

    public final int Line;

    public final String Text;

    //TODO Style, RightClickListener, LeftClickListener, OnMouseEnterListener, OnMouseELeaveListener


    public SourceViewInsertion(@Nonnull String group, int line, @Nonnull String text) {
        Group = group;
        Line = line;
        Text = text;
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
}
