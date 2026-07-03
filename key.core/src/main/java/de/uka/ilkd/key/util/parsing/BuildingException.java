/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import java.net.URI;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;
import org.key_project.util.parsing.SourceNames;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (3/27/20)
 */
public class BuildingException extends RuntimeException implements HasLocation {
    private final @Nullable Token offendingSymbol;

    /**
     * An optional position that overrides the position derived from {@link #offendingSymbol}. This
     * is used when the real error location is not the offending token itself but a more precise
     * spot, e.g. a position <em>inside</em> a Java block that is represented by a single token
     * (the modality), but whose URI is still the one of that token.
     */
    private final @Nullable Position overridePosition;

    /**
     * The message as passed in, <em>without</em> the " at &lt;file&gt;:&lt;line&gt;:&lt;col&gt;"
     * suffix that {@link #getMessage()} appends. Consumers that render the {@link #getLocation()}
     * separately (the GUI dialog, the console formatter) should use this to avoid printing the
     * position twice.
     */
    private final @Nullable String rawMessage;

    /**
     * A location supplied explicitly (rather than derived from an offending token), e.g. the
     * {@code \classpath} declaration in a {@code .key} file whose directory does not exist.
     */
    private final @Nullable Location explicitLocation;

    public BuildingException(ParserRuleContext ctx, String format) {
        this(ctx, format, null);
    }

    public BuildingException(Throwable e) {
        super(e);
        offendingSymbol = null;
        overridePosition = null;
        explicitLocation = null;
        rawMessage = e == null ? null : e.getMessage();
    }

    /**
     * Creates an exception carrying an explicit {@link Location} (file + position), for errors
     * whose
     * origin is a declaration in a {@code .key} file rather than an offending parser token - e.g. a
     * missing {@code \classpath}/{@code \bootclasspath} directory.
     *
     * @param location the location (file and position) of the offending declaration
     * @param message the error message
     */
    public BuildingException(Location location, String message) {
        super(message + locationSuffix(location));
        offendingSymbol = null;
        overridePosition = null;
        explicitLocation = location;
        rawMessage = message;
    }

    private static String locationSuffix(@Nullable Location location) {
        if (location == null || location.getFileURI().isEmpty()
                || location.getPosition().isNegative()) {
            return "";
        }
        return " at " + location.getFileUri() + ":" + location.getPosition().line() + ":"
            + location.getPosition().column();
    }

    public BuildingException(ParserRuleContext ctx, String message, Throwable e) {
        this(ctx == null ? null : ctx.start, message, e);
    }

    public BuildingException(@Nullable Token t, String message, Throwable e) {
        this(t, null, message, e);
    }

    /**
     * Creates an exception whose location uses the URI of the given token but the explicitly
     * provided position instead of the token's own position.
     *
     * @param t the token providing the source (file) of the error, may be null
     * @param overridePosition the precise position of the error, or null to use the token's
     *        position
     * @param message the error message
     * @param e the causing throwable, may be null
     */
    public BuildingException(@Nullable Token t, @Nullable Position overridePosition, String message,
            Throwable e) {
        super(message + " at " + getPosition(t, overridePosition), e);
        offendingSymbol = t;
        this.overridePosition = overridePosition;
        this.explicitLocation = null;
        this.rawMessage = message;
    }

    /**
     * The error message without the trailing " at &lt;position&gt;" suffix. Use this together with
     * {@link #getLocation()} to avoid reporting the position twice.
     */
    public String getRawMessage() {
        return rawMessage != null ? rawMessage : getMessage();
    }

    private static String getPosition(@Nullable Token t) {
        return getPosition(t, null);
    }

    private static String getPosition(@Nullable Token t, @Nullable Position override) {
        if (t != null) {
            var p = override != null ? override : Position.fromToken(t);
            return t.getTokenSource().getSourceName() + ":" + p.line() + ":" + p.column();
        } else {
            return "";
        }
    }

    public BuildingException(ParserRuleContext ctx, Throwable ex) {
        this(ctx.start, ex.getMessage(), ex);
    }

    @Override
    public String toString() {
        return getMessage() + " (" + getPosition(offendingSymbol, overridePosition) + ")";
    }

    @Override
    public Location getLocation() {
        if (explicitLocation != null) {
            return explicitLocation;
        }
        if (offendingSymbol != null) {
            URI uri = SourceNames.getURIFromTokenSource(offendingSymbol.getTokenSource());
            Position p = overridePosition != null ? overridePosition
                    : Position.fromToken(offendingSymbol);
            return new Location(uri, p);
        }
        return Location.UNDEFINED;
    }
}
