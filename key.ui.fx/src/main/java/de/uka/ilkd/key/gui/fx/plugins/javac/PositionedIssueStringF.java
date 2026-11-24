/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.plugins.javac;

import java.util.Objects;

import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NonNull;

/**
 * Small data class that in addition to the information already contained by {@link
 * PositionedString} (text, filename, position) contains a String for additional information which
 * can be used to store a stacktrace if present. FX port of the Swing {@code PositionedIssueString}
 * (key.ui {@code gui/PositionedIssueString.java} — not reachable from this module).
 *
 * @see JavaCompilerCheckFacadeF
 */
public class PositionedIssueStringF extends PositionedString
        implements Comparable<PositionedIssueStringF> {

    public enum Kind {
        ERROR, WARNING, INFO
    }

    /**
     * contains additional information, e.g., a stacktrace
     */
    private final @NonNull String additionalInfo;

    private final Kind kind;

    public PositionedIssueStringF(@NonNull String text, @NonNull Location location,
            @NonNull String additionalInfo) {
        this(text, location, additionalInfo, Kind.ERROR);
    }

    public PositionedIssueStringF(@NonNull String text, @NonNull Location location,
            @NonNull String additionalInfo, Kind kind) {
        super(text, location);
        this.additionalInfo = additionalInfo;
        this.kind = kind;
    }

    public PositionedIssueStringF(@NonNull String text) {
        this(text, Location.UNDEFINED, "", Kind.ERROR);
    }

    public PositionedIssueStringF(@NonNull PositionedString o, @NonNull String additionalInfo) {
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
        PositionedIssueStringF that = (PositionedIssueStringF) o;
        return additionalInfo.equals(that.additionalInfo) && kind.equals(that.kind);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), additionalInfo, kind);
    }

    @Override
    public int compareTo(PositionedIssueStringF o) {
        int compareLocation = location.compareTo(o.location);
        if (compareLocation != 0) {
            return compareLocation;
        }
        return kind.compareTo(o.kind);
    }
}
