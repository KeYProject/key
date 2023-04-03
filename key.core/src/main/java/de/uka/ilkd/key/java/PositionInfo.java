package de.uka.ilkd.key.java;

import java.net.URI;
import java.nio.file.Paths;

import recoder.java.SourceElement;

/**
 * represents a group of three Positions: relativePosition, startPosition, endPosition
 *
 * 2019-09-10 Wolfram Pfeifer: work with URIs instead of Strings -> more robust, more general
 */
public class PositionInfo {
    /** Unknown URI (enables us to always have a non-null value for fileURI) */
    public static final URI UNKNOWN_URI = URI.create("UNKNOWN://unknown");

    /** PositionInfo with undefined positions. */
    public static final PositionInfo UNDEFINED = new PositionInfo();

    /**
     * TODO: What is the purpose of this? To which position is this one relative?
     */
    private final SourceElement.Position relPos;

    /** The start position. */
    private final Position startPos;

    /** The end position. */
    private final Position endPos;

    /**
     * The URI of the resource this location refers to. Either a meaningful value or
     * {@link #UNKNOWN_URI}, but never null.
     */
    private final URI fileURI;

    /**
     * The URI of the parent class of this location (the class the statement originates from). May
     * be null.
     */
    private URI parentClassURI;

    private PositionInfo() {
        this.relPos = SourceElement.Position.UNDEFINED;
        this.startPos = Position.UNDEFINED;
        this.endPos = Position.UNDEFINED;
        fileURI = UNKNOWN_URI;
    }

    /**
     * Creates a new PositionInfo without resource information but only with positions.
     *
     * @param relPos the relative position
     * @param startPos the start position
     * @param endPos the end position
     */
    public PositionInfo(SourceElement.Position relPos, Position startPos, Position endPos) {
        this.relPos = relPos;
        this.startPos = startPos;
        this.endPos = endPos;
        fileURI = UNKNOWN_URI;
    }

    /**
     * Creates a new PositionInfo without the given resource information.
     *
     * @param relPos the relative position
     * @param startPos the start position
     * @param endPos the end position
     * @param fileURI the resource the PositionInfo refers to
     */
    public PositionInfo(SourceElement.Position relPos, Position startPos, Position endPos,
            URI fileURI) {
        this.relPos = relPos;
        this.startPos = startPos;
        this.endPos = endPos;
        if (fileURI == null) {
            this.fileURI = UNKNOWN_URI; // fileURI must not be null!
        } else {
            this.fileURI = fileURI.normalize();
        }
    }

    /**
     * this violates immutability, but the method is only called right after the object is
     * created...
     *
     * @param parent the parent class of this PositionInfo
     */
    void setParentClassURI(URI parent) {
        parentClassURI = (parent == null ? null : parent.normalize());
    }

    /**
     * Returns the path of the parent file the PositionInfo refers to (the class the statement
     * originates from).
     *
     * @deprecated This method should no longer be used, as PositionInfo can now be used with
     *             resources other than files. Use {@link #getParentClassURI()} instead.
     * @return the filename as a string if parentClass uses the "file" protocol or null otherwise
     */
    @Deprecated // only kept for compatibility reasons
    public String getParentClass() {
        if (parentClassURI != null && parentClassURI.getScheme().equals("file")) {
            return Paths.get(parentClassURI).toString();
        }
        return null;
    }

    /**
     * Returns the path of the file the PositionInfo refers to.
     *
     * @deprecated This method should no longer be used, as PositionInfo can now be used with
     *             resources other than files. Use {@link #getURI()} instead.
     * @return the filename as a string if fileURI uses the "file" protocol or null otherwise
     */
    @Deprecated // only kept for compatibility reasons
    public String getFileName() {
        if (fileURI.getScheme().equals("file")) {
            return Paths.get(fileURI).toString();
        }
        return null;
    }

    public URI getParentClassURI() {
        return parentClassURI;
    }

    public URI getURI() {
        return fileURI;
    }

    public SourceElement.Position getRelativePosition() {
        return relPos;
    }

    public Position getStartPosition() {
        return startPos;
    }

    public Position getEndPosition() {
        return endPos;
    }

    /**
     * Creates a new PositionInfo from joining the intervals of the given PositionInfos. The file
     * information have to match, otherwise null is returned.
     *
     * @param p1 the first PositionInfo
     * @param p2 the second PositionInfo
     * @return a new PositionInfo starting at the minimum of the two start positions and ending at
     *         the maximum of the two end positions.
     */
    public static PositionInfo join(PositionInfo p1, PositionInfo p2) {
        if (p1 == null && p2 == null) {
            return null;
        } else if (p1 == null) {
            return p2;
        } else if (p2 == null) {
            return p1;
        }

        // -> p1 and p2 not null
        if (p1 == UNDEFINED) {
            return p2;
        } else if (p2 == UNDEFINED) {
            return p1;
        }

        // -> p1 and p2 != UNDEFINED
        Position start;
        Position end;
        if (p1.startPos != Position.UNDEFINED && !p1.startPos.isNegative()
                && p1.startPos.compareTo(p2.startPos) < 0) {
            start = p1.startPos;
        } else {
            start = p2.startPos;
        }
        if (p1.endPos != Position.UNDEFINED && !p1.endPos.isNegative()
                && p1.endPos.compareTo(p2.endPos) > 0) {
            end = p1.endPos;
        } else {
            end = p2.endPos;
        }
        // TODO: join relative position as well
        return new PositionInfo(SourceElement.Position.UNDEFINED, start, end, p1.getURI());
    }

    /**
     * Checks if start and end position are both defined and in valid range.
     *
     * @return true iff start and end are valid
     */
    public boolean startEndValid() {
        return startPos != Position.UNDEFINED && !startPos.isNegative()
                && endPos != Position.UNDEFINED && !endPos.isNegative();
    }

    @Override
    public String toString() {
        if (this == PositionInfo.UNDEFINED) {
            return "UNDEFINED";
        } else {
            return ((fileURI == UNKNOWN_URI ? "" : fileURI) + " rel. Pos: " + relPos
                + " start Pos: " + startPos + " end Pos: " + endPos);
        }
    }

}
