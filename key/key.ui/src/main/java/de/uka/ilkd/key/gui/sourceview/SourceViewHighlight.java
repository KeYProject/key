package de.uka.ilkd.key.gui.sourceview;


import de.uka.ilkd.key.pp.Range;

import javax.swing.text.Highlighter;
import java.awt.*;
import java.net.URI;
import java.util.HashMap;
import java.util.Map;

/**
 * <p>
 * An object of this class represents a highlight of a specific line in the {@code SourceView}.
 * </p>
 *
 * @author lanzinger
 *
 * @see SourceView#addHighlight(URI, int, Color, int)
 * @see SourceView#changeHighlight(SourceViewHighlight, int)
 * @see SourceView#removeHighlight(SourceViewHighlight)
 */
public final class SourceViewHighlight implements Comparable<SourceViewHighlight> {

    /** @see #getLevel() */
    final String group;

    /** @see #getTag() */
    static final Map<SourceViewHighlight, Object> TAGS = new HashMap<>();

    /** @see #getLevel() */
    final int level;

    /** @see #getColor() */
    final Color color;

    /** @see #getFileURI() */
    final URI fileURI;

    /** @see #getSourceLine() */
    final int sourceLine;

    /** @see #getPatchedLine() */
    final int patchedLine;

    /** @see #getPatchedRange() */
    final Range patchedRange;

    /**
     * Creates a new highlight.
     *
     * @param fileURI URI of the file in which this highlight is used.
     * @param sourceLine the line being highlighted (in source, can be -1).
     * @param patchedLine the line being highlighted (in actual displayed content).
     * @param patchedRange the range being highlighted (in actual displayed content).
     * @param color this highlight's color.
     * @param level this highlight's level.
     */
    SourceViewHighlight(String group,
                        URI fileURI,
                        int sourceLine,
                        int patchedLine,
                        Range patchedRange,
                        Color color,
                        int level) {
        this.group = group;
        this.level = level;
        this.color = color;
        this.fileURI = fileURI;
        this.sourceLine = sourceLine;
        this.patchedLine = patchedLine;
        this.patchedRange = patchedRange;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((color == null) ? 0 : color.hashCode());
        result = prime * result + ((fileURI == null) ? 0 : fileURI.hashCode());
        result = prime * result + level;
        result = prime * result + sourceLine;
        result = prime * result + patchedLine;
        result = prime * result + patchedRange.hashCode();
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        SourceViewHighlight other = (SourceViewHighlight) obj;
        if (color == null) {
            if (other.color != null) {
                return false;
            }
        } else if (!color.equals(other.color)) {
            return false;
        }
        if (fileURI == null) {
            if (other.fileURI != null) {
                return false;
            }
        } else if (!fileURI.equals(other.fileURI)) {
            return false;
        }
        if (level != other.level) {
            return false;
        }
        if (sourceLine != other.sourceLine) {
            return false;
        }
        if (patchedLine != other.patchedLine) {
            return false;
        }
        if (!patchedRange.equals(other.patchedRange)) {
            return false;
        }
        return true;
    }

    @Override
    public int compareTo(SourceViewHighlight other) {
        int result = fileURI.compareTo(other.fileURI);

        if (result == 0) {
            result = Integer.compare(patchedLine, other.patchedLine);
        }

        if (result == 0) {
            result = Integer.compare(level, other.level);
        }

        if (result == 0) {
            result = Integer.compare(sourceLine, other.sourceLine);
        }

        if (result == 0) {
            result = Integer.compare(color.getRGB(), other.color.getRGB());
        }

        if (result == 0) {
            result = Integer.compare(patchedRange.start(), other.patchedRange.start());
        }

        if (result == 0) {
            result = Integer.compare(patchedRange.end(), other.patchedRange.end());
        }

        return result;
    }

    /**
     *
     * @param tag the new tag wrapped by this object.
     *
     * @see Highlighter#addHighlight(int, int, Highlighter.HighlightPainter)
     * @see Highlighter#changeHighlight(Object, int, int)
     * @see Highlighter#removeHighlight(Object)
     */
    void setTag(Object tag) {
        if (tag == null) {
            TAGS.remove(this);
        } else {
            TAGS.put(this, tag);
        }
    }

    /**
     *
     * @return the tag wrapped by this object.
     *
     * @see Highlighter#addHighlight(int, int, Highlighter.HighlightPainter)
     * @see Highlighter#changeHighlight(Object, int, int)
     * @see Highlighter#removeHighlight(Object)
     */
    Object getTag() {
        return TAGS.get(this);
    }

    /**
     *
     * @return this highlight's level.
     */
    public int getLevel() {
        return level;
    }

    /**
     *
     * @return this highlight's color.
     */
    public Color getColor() {
        return color;
    }

    /**
     *
     * @return the file in which this highlight is used.
     */
    public URI getFileURI() {
        return fileURI;
    }

    /**
     *
     * @return the line being highlighted.
     */
    public int getSourceLine() {
        return sourceLine;
    }

    /**
     *
     * @return the line being highlighted.
     */
    public int getPatchedLine() {
        return patchedLine;
    }

    /**
     * @return the range (in sourceview).
     */
    public Range getPatchedRange() {
        return patchedRange;
    }

    /**
     *
     * @return this group
     */
    public String getGroup() {
        return group;
    }
}
