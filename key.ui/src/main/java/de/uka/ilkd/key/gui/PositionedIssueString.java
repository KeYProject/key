/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.Objects;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;

import org.jspecify.annotations.NonNull;

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
    private final @NonNull String additionalInfo;

    private final Kind kind;

    public PositionedIssueString(@NonNull String text, @NonNull Location location,
            @NonNull String additionalInfo) {
        this(text, location, additionalInfo, Kind.ERROR);
    }

    public PositionedIssueString(@NonNull String text, @NonNull Location location,
            @NonNull String additionalInfo, Kind kind) {
        super(text, location);
        this.additionalInfo = additionalInfo;
        this.kind = kind;
    }

    public PositionedIssueString(@NonNull String text) {
        this(text, new Location(null, Position.UNDEFINED), "", Kind.ERROR);
    }

    public PositionedIssueString(@NonNull PositionedString o, @NonNull String additionalInfo) {
        this(o.text, o.location, additionalInfo, Kind.ERROR);
    }

    public Kind getKind() {
        return kind;
    }

    public @NonNull String getAdditionalInfo() {
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
        int compareLocation = location.compareTo(o.location);
        if (compareLocation != 0) {
            return compareLocation;
        }
        return kind.compareTo(o.kind);
    }
}
