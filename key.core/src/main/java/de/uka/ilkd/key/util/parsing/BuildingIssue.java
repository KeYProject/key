/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.parsing;

import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

public class BuildingIssue {
    private final String message;
    private final Position position;
    private final @Nullable Throwable cause;
    private final boolean isWarning;

    public BuildingIssue(String message, @Nullable Throwable cause, boolean isWarning,
            Position position) {
        this.message = message;
        this.position = position;
        this.cause = cause;
        this.isWarning = isWarning;
    }

    public static BuildingIssue createError(String message, @Nullable ParserRuleContext token,
            @Nullable Throwable cause) {
        return createError(message, token != null ? token.start : null, cause);
    }

    private static BuildingIssue fromToken(String message, boolean isWarning, @Nullable Token token,
            @Nullable Throwable cause) {
        if (token != null) {
            var position = Position.fromToken(token);
            return new BuildingIssue(message, cause, isWarning, position);
        }
        return new BuildingIssue(message, cause, isWarning, Position.UNDEFINED);
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

    public Position getPosition() {
        return position;
    }

    public boolean isWarning() {
        return isWarning;
    }

    public String getMessage() {
        return message;
    }
}
