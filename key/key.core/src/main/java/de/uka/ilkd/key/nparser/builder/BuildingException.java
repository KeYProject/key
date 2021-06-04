package de.uka.ilkd.key.nparser.builder;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (3/27/20)
 */
public class BuildingException extends RuntimeException {
    public BuildingException(ParserRuleContext ctx, String format) {
        this(ctx, format, null);
    }

    public BuildingException(Throwable e) {
        super(e);
    }

    public BuildingException(ParserRuleContext ctx, String format, Throwable e) {
        this(ctx == null ? null : ctx.start, format, e);
    }

    public BuildingException(Token t, String format, Throwable e) {
        super(format + getPosition(t), e);
    }

    private static String getPosition(Token t) {
        if (t != null) {
            return t.getTokenSource().getSourceName() + ":" + t.getLine() + ":" + t.getCharPositionInLine();
        } else return "";
    }

    public BuildingException(ParserRuleContext ctx, Throwable ex) {
        this(ctx.start, "", ex);
    }
}
