/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.net.URI;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.Nullable;

/**
 * A construct of the input being loaded is not supported by KeY's JML/Java translation, e.g.
 * {@code assignable bucketData[*][*];} or {@code int[][] a = new int[n][];}.
 * <p>
 * The exception carries the 1-based source position and the exact source snippet of the construct,
 * so that front-ends can report the stable, structured diagnostic
 * {@code <file>:<line>:<col>: construct '<snippet>' not supported: <reason>} instead of the
 * {@code NullPointerException}/{@code ClassCastException} the translation used to crash with.
 * <p>
 * It is thrown while the problem is loaded and therefore surfaces in the cause chain of the
 * surrounding {@link ProblemLoaderException}; consumers (e.g. the headless CLI) should report it
 * verbatim as an input error.
 */
public final class ConstructNotSupportedException extends RuntimeException implements HasLocation {

    /** Placeholder for the file part of the diagnostic when the source file is unknown. */
    public static final String UNKNOWN_FILE = "?";

    private final String file;
    private final int line;
    private final int column;
    private final String snippet;
    private final String reason;

    /**
     * Creates a new unsupported-construct diagnostic.
     *
     * @param file human-readable reference to the source file (path or URI), never {@code null}
     * @param line the 1-based line of the construct in the source file ({@code 0} if unknown)
     * @param column the 1-based column of the construct in the source file ({@code 0} if unknown)
     * @param snippet the exact source text of the unsupported construct
     * @param reason why the construct is not supported
     */
    public ConstructNotSupportedException(String file, int line, int column, String snippet,
            String reason) {
        super(formatMessage(file, line, column, snippet, reason));
        this.file = file;
        this.line = line;
        this.column = column;
        this.snippet = snippet;
        this.reason = reason;
    }

    /**
     * @return the human-readable reference to the source file
     */
    public String file() {
        return file;
    }

    /**
     * @return the 1-based line of the construct in the source file ({@code 0} if unknown)
     */
    public int line() {
        return line;
    }

    /**
     * @return the 1-based column of the construct in the source file ({@code 0} if unknown)
     */
    public int column() {
        return column;
    }

    /**
     * @return the exact source text of the unsupported construct
     */
    public String snippet() {
        return snippet;
    }

    /**
     * @return why the construct is not supported
     */
    public String reason() {
        return reason;
    }

    /**
     * @return the structured diagnostic
     *         {@code <file>:<line>:<col>: construct '<snippet>' not supported: <reason>}
     *         (identical to {@link #getMessage()})
     */
    public String formattedMessage() {
        return formatMessage(file, line, column, snippet, reason);
    }

    /**
     * {@inheritDoc}
     * <p>
     * The location is {@code null} when the source position is unknown (line or column {@code 0}),
     * e.g. for synthetic nodes without a token range.
     */
    @Override
    public @Nullable Location getLocation() {
        if (line <= 0 || column <= 0) {
            return null;
        }
        return new Location(fileUri(), Position.newOneBased(line, column));
    }

    /**
     * Converts the stored file reference (a path, a {@code file:} URI, or any other URI) to a URI.
     * Paths become absolute {@code file:} URIs; an unknown file yields {@code null}.
     */
    private @Nullable URI fileUri() {
        if (UNKNOWN_FILE.equals(file) || file.isBlank()) {
            return null;
        }
        try {
            URI uri = URI.create(file);
            if (uri.getScheme() != null) {
                return uri;
            }
        } catch (IllegalArgumentException e) {
            // not a URI: treat the reference as a path below
        }
        try {
            Path path = Paths.get(file);
            return path.toAbsolutePath().toUri();
        } catch (IllegalArgumentException e) {
            return null;
        }
    }

    private static String formatMessage(String file, int line, int column, String snippet,
            String reason) {
        return file + ":" + line + ":" + column + ": construct '" + snippet
            + "' not supported: " + reason;
    }

    /**
     * Converts a source file URI (as carried by ANTLR char streams) to a human-readable path
     * string: {@code file:} URIs become file paths, anything else stays a URI string.
     *
     * @param uri the source file URI, or {@code null}
     * @return the path string, or {@link #UNKNOWN_FILE} for {@code null}
     */
    public static String displayFile(@Nullable URI uri) {
        if (uri == null) {
            return UNKNOWN_FILE;
        }
        if ("file".equalsIgnoreCase(uri.getScheme())) {
            try {
                return Paths.get(uri).toString();
            } catch (IllegalArgumentException e) {
                return uri.toString();
            }
        }
        return uri.toString();
    }
}
