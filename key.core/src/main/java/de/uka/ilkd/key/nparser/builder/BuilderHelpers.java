package de.uka.ilkd.key.nparser.builder;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import javax.annotation.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public final class BuilderHelpers {
    public static String getPosition(@Nullable ParserRuleContext node) {
        if (node == null)
            return " pos n/a";
        return getPosition(node.start);
    }

    public static String getPosition(@Nullable Token t) {
        return t == null ? " pos n/a"
                : String.format(" %s:%d#%d", t.getInputStream().getSourceName(), t.getLine(),
                    t.getCharPositionInLine());
    }

}
