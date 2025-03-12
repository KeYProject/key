/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 *
 */
public record Position(String source, int line, int charInLine, int startOffset, int length) {

    public static Position make(ParserRuleContext ctx) { return make(ctx.start); }

    public static Position make(Token ctx) {
        return new Position(ctx.getTokenSource().getSourceName(), ctx.getLine(),
            ctx.getCharPositionInLine(), ctx.getStartIndex(),
            ctx.getStopIndex() - ctx.getStartIndex()/*
                                                     * maybe
                                                     * +1
                                                     */);
    }
}
