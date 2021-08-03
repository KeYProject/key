package de.uka.ilkd.key.util.parsing;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.MiscTools;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

/**
 * @author Alexander Weigl
 * @version 1 (3/27/20)
 */
public class BuildingException extends RuntimeException implements HasLocation {
    private final @Nullable
    Token offendingSymbol;

    public BuildingException(ParserRuleContext ctx, String format) {
        this(ctx, format, null);
    }

    public BuildingException(Throwable e) {
        super(e);
        offendingSymbol = null;
    }

    public BuildingException(ParserRuleContext ctx, String format, Throwable e) {
        this(ctx == null ? null : ctx.start, format, e);
    }

    public BuildingException(@Nullable Token t, String format, Throwable e) {
        super(format + getPosition(t), e);
        offendingSymbol = t;
    }

    private static String getPosition(Token t) {
        if (t != null) {
            return t.getTokenSource().getSourceName() + ":" + t.getLine() + ":" + t.getCharPositionInLine();
        } else return "";
    }

    public BuildingException(ParserRuleContext ctx, Throwable ex) {
        this(ctx.start, "", ex);
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        if (offendingSymbol != null) {
            return new Location(MiscTools.parseURL(
                    offendingSymbol.getTokenSource().getSourceName()),
                    offendingSymbol.getLine(),
                    offendingSymbol.getCharPositionInLine());
        }
        return null;
    }
}
