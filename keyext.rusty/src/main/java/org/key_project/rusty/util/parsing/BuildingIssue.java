/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.util.parsing;

import org.key_project.rusty.util.Position;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.Nullable;

public record BuildingIssue(String message, @Nullable Throwable cause, boolean isWarning,
                            Position position,
                            @Nullable String sourceName) {

    public static BuildingIssue createError(String message, @Nullable ParserRuleContext token, @Nullable Throwable cause) {
        return createError(message, token != null ? token.start : null, cause);
    }

    private static BuildingIssue fromToken(String message, boolean isWarning, @Nullable Token token, @Nullable Throwable cause) {
        if (token != null) {
            var position = Position.make(token);
            return new BuildingIssue(message, cause, isWarning, position, token.getTokenSource().getSourceName());
        }
        return new BuildingIssue(message, cause, isWarning, null, null);
    }

    public static BuildingIssue createError(String message, @Nullable Token token, @Nullable Throwable cause) {
        return fromToken(message, false, token, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable ParserRuleContext token, @Nullable Throwable cause) {
        return createWarning(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable Token token, @Nullable Throwable cause) {
        return fromToken(message, true, token, cause);
    }
}
