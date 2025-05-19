/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.net.URI;
import java.util.Objects;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.parser.Location;

import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A string with associated position information (file and line number). The position information is
 * used for error reporting.
 */
@NullMarked
public class PositionedString {
    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST = new ImmutableArray<>();

    public final String text;
    public final Location location;

    public PositionedString(String text, Location location) {
        this.text = Objects.requireNonNull(text);
        this.location = Objects.requireNonNull(location);
    }

    public PositionedString(String text, org.antlr.v4.runtime.Token t) {
        this(text, Location.fromToken(t));
    }

    public PositionedString(String text, @Nullable URI fileName) {
        this(text, new Location(fileName, Position.UNDEFINED));
    }

    public PositionedString(String text) {
        this(text, (URI) null);
    }

    /**
     * Returns true, if the position information contains a file name.
     */
    public boolean hasFilename() {
        return location.getFileURI().isPresent();
    }

    public PositionedString prepend(String text) {
        return new PositionedString(text + this.text.trim(), location);
    }


    public String toString() {
        return text + " ("
            + (location.getFileURI().isPresent() ? location.getFileURI().get() + ", " : "")
            + location.getPosition() + ")";
    }

    public @NonNull String getText() {
        return text;
    }

    public @NonNull Location getLocation() {
        return location;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof PositionedString that)) {
            return false;
        }
        return text.equals(that.text) && Objects.equals(location, that.location);
    }

    @Override
    public int hashCode() {
        return Objects.hash(text, location);
    }

    /**
     * returns true if the positioned string is labeled
     */
    public boolean hasLabels() {
        return false;
    }

    /**
     * checks if the given label is attached to the positioned string
     *
     * @param label the ITermLabel for which to look (must not be null)
     */
    public boolean containsLabel(TermLabel label) {
        return false;
    }

    /**
     * returns list of labels attached to this positioned string
     *
     * @return list of labels (maybe be empty but never <code>null</code>
     */
    public ImmutableArray<TermLabel> getLabels() {
        return EMPTY_LABEL_LIST;
    }

    public PositionedLabeledString label(ImmutableArray<TermLabel> labels) {
        return new PositionedLabeledString(text, location, labels);
    }

    public PositionedLabeledString label(TermLabel label) {
        return new PositionedLabeledString(text, location, label);
    }
}
