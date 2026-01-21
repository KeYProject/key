package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.util.Debug;
import org.antlr.runtime.Token;
import org.key_project.util.collection.ImmutableArray;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Objects;

/**
 * A string with associated position information (file and line number). The position information is
 * used for error reporting.
 */
public class PositionedString {
    private static final Logger LOGGER = LoggerFactory.getLogger(PositionedString.class);

    public static final String UNDEFINED_FILE = "<unknown>";

    @Nonnull
    public final String text;

    @Nonnull
    public final String fileName;

    @Nonnull
    public final Position pos;

    private static final ImmutableArray<TermLabel> EMPTY_LABEL_LIST = new ImmutableArray<>();

    public PositionedString(@Nonnull String text, @Nullable String fileName,
            @Nullable Position pos) {
        if (text == null) {
            throw new IllegalArgumentException();
        }

        if (fileName == null) {
            fileName = UNDEFINED_FILE;
        }
        if (pos == null) {
            pos = Position.UNDEFINED;
        }
        this.text = text;
        this.fileName = fileName;
        this.pos = pos;
    }

    public PositionedString(@Nonnull String text, Token t) {
        this(text, t.getInputStream().getSourceName(),
            new Position(t.getLine(), t.getCharPositionInLine()));
    }

    public PositionedString(@Nonnull String text, String fileName) {
        this(text, fileName, null);
    }


    public PositionedString(String text) {
        this(text, (String) null);
    }

    /**
     * Returns true, if the position information contains a file name.
     */
    public boolean hasFilename() {
        return fileName != null && !fileName.isEmpty() && !fileName.equals(UNDEFINED_FILE);
    }


    public PositionedString prependAndUpdatePosition(String text) {
        if (this.pos.getColumn() < text.length()) {
            LOGGER.debug("Column of given position " + pos + " is smaller than prepended text "
                + "\"" + text + "\". This will result in a negative column value for " + "returned "
                + PositionedString.class.getSimpleName() + ".");
        }
        Position newPos = new Position(this.pos.getLine(), this.pos.getColumn() - text.length());
        return new PositionedString(text + this.text, this.fileName, newPos);
    }

    public PositionedString prepend(String text) {
        return new PositionedString(text + this.text.trim(), this.fileName, this.pos);
    }


    public String toString() {
        return text + " (" + fileName + ", " + pos + ")";
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
        return text.equals(that.text) && Objects.equals(fileName, that.fileName)
                && Objects.equals(pos, that.pos);
    }

    @Override
    public int hashCode() {
        return Objects.hash(text, fileName, pos);
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
        return new PositionedLabeledString(text, fileName, pos, labels);
    }

    public PositionedLabeledString label(TermLabel label) {
        return new PositionedLabeledString(text, fileName, pos, label);
    }
}
