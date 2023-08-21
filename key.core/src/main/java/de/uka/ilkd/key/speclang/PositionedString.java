/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.net.URI;
import java.util.Objects;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.parser.Location;

import org.key_project.util.collection.ImmutableArray;

/**
 * A string with associated position information (file and line number). The position information is
 * used for error reporting.
 */
public class PositionedString {
    @Nonnull
    public final String text;

    @Nonnull
    public final Location location;

    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST = new ImmutableArray<>();

    public PositionedString(@Nonnull String text, @Nonnull Location location) {
        if (text == null || location == null) {
            throw new IllegalArgumentException();
        }

        this.text = text;
        this.location = location;
    }

    public PositionedString(@Nonnull String text, URI fileName) {
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

    @Nonnull
    public String getText() {
        return text;
    }

    @Nonnull
    public Location getLocation() {
        return location;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof PositionedString)) {
            return false;
        }
        PositionedString that = (PositionedString) o;
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
