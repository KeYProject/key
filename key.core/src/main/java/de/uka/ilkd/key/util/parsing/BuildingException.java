package de.uka.ilkd.key.util.parsing;

import java.net.MalformedURLException;
import java.net.URL;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (3/27/20)
 */
public class BuildingException extends RuntimeException implements HasLocation {
    private final @Nullable Token offendingSymbol;

    public BuildingException(ParserRuleContext ctx, String format) {
        this(ctx, format, null);
    }

    public BuildingException(Throwable e) {
        super(e);
        offendingSymbol = null;
    }

    public BuildingException(ParserRuleContext ctx, String message, Throwable e) {
        this(ctx == null ? null : ctx.start, message, e);
    }

    public BuildingException(@Nullable Token t, String message, Throwable e) {
        super(message + " at " + getPosition(t), e);
        offendingSymbol = t;
    }

    private static String getPosition(Token t) {
        if (t != null) {
            var p = Position.fromToken(t);
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
        return getMessage() + " (" + getPosition(offendingSymbol) + ")";
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        if (offendingSymbol != null) {
            var source = offendingSymbol.getTokenSource().getSourceName();
            URL url = null;
            if (!IntStream.UNKNOWN_SOURCE_NAME.equals(source)) {
                url = MiscTools.parseURL(source);
            }
            return new Location(url, Position.fromToken(offendingSymbol));
        }
        return null;
    }
}
