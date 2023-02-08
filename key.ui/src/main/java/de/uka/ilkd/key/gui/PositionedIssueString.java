package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Objects;

/**
 * Small data class that in addition to the information already contained by PositionedString
 * (text, filename, position) contains a String for additional information which can be used to
 * store a stacktrace if present.
 */
public class PositionedIssueString extends PositionedString
        implements Comparable<PositionedIssueString> {

    public enum Kind {
        ERROR, WARNING, INFO
    }

    /**
     * contains additional information, e.g., a stacktrace
     */
    private final @Nonnull String additionalInfo;

    private final Kind kind;

    public PositionedIssueString(@Nonnull String text, @Nullable String fileName,
            @Nullable Position pos, @Nonnull String additionalInfo) {
        this(text, fileName, pos, additionalInfo, Kind.ERROR);
    }

    public PositionedIssueString(@Nonnull String text, @Nullable String fileName,
            @Nullable Position pos, @Nonnull String additionalInfo, Kind kind) {
        super(text, fileName, pos);
        this.additionalInfo = additionalInfo;
        this.kind = kind;
    }

    public PositionedIssueString(@Nonnull String text) {
        this(text, null, null, "", Kind.ERROR);
    }

    public PositionedIssueString(@Nonnull PositionedString o, @Nonnull String additionalInfo) {
        this(o.text, o.fileName, o.pos, additionalInfo, Kind.ERROR);
    }

    public Kind getKind() {
        return kind;
    }

    @Nonnull
    public String getAdditionalInfo() {
        return additionalInfo;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        if (!super.equals(o)) {
            return false;
        }
        PositionedIssueString that = (PositionedIssueString) o;
        return additionalInfo.equals(that.additionalInfo) && kind.equals(that.kind);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), additionalInfo, kind);
    }

    @Override
    public int compareTo(PositionedIssueString o) {
        int compareFile = fileName.compareTo(o.fileName);
        if (compareFile != 0) {
            return compareFile;
        }
        int comparePosition = pos.compareTo(o.pos);
        if (comparePosition != 0) {
            return comparePosition;
        }
        return kind.compareTo(o.kind);
    }
}
