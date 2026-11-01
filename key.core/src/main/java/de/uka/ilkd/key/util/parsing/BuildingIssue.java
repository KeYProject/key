/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.util.parsing;

import java.net.URI;

import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public record BuildingIssue(String message, @Nullable Throwable cause, boolean isWarning,
        Position position, @Nullable String sourceName) {

    public static BuildingIssue createError(String message, @Nullable ParserRuleContext token,
            @Nullable Throwable cause) {
        return createError(message, token != null ? token.start : null, cause);
    }

    private static BuildingIssue fromToken(String message, boolean isWarning, @Nullable Token token,
            @Nullable Throwable cause) {
        if (token != null) {
            var position = Position.fromToken(token);
            return new BuildingIssue(message, cause, isWarning, position,
                token.getTokenSource().getSourceName());
        }
        return new BuildingIssue(message, cause, isWarning, Position.UNDEFINED, null);
    }

    public static BuildingIssue createError(String message, @Nullable Token token,
            @Nullable Throwable cause) {
        return fromToken(message, false, token, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable ParserRuleContext token,
            @Nullable Throwable cause) {
        return createWarning(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable Token token,
            @Nullable Throwable cause) {
        return fromToken(message, true, token, cause);
    }

    /**
     * The source location of this issue (file + position). The file may be absent if the source
     * cannot be resolved to a URL; the position may be {@link Position#UNDEFINED}.
     */
    public Location getLocation() {
        URI uri = null;
        if (sourceName != null) {
            try {
                uri = MiscTools.parseURL(sourceName).toURI();
            } catch (Exception e) {
                uri = null;
            }
        }
        // A source may not resolve to a file URI (e.g. "memory:/" Java block fragments), but the
        // position is still meaningful — the underline must anchor on the offending code, not on
        // the surrounding token. Location's fileUri component may be null (see Location javadoc);
        // like Location.UNDEFINED / Location.fromToken, the null file is a legitimate value.
        return location(uri, position);
    }

    private static Location location(@Nullable URI uri, Position position) {
        return uri != null ? new Location(uri, position) : Location.UNDEFINED;
    }

    public PositionedString asPositionedString() {
        return new PositionedString(message, getLocation());
    }
}
