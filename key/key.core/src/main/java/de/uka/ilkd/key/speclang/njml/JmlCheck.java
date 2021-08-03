package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.speclang.PositionedString;
import org.antlr.v4.runtime.ParserRuleContext;

import javax.annotation.Nonnull;
import java.util.List;

/**
 * Interface describes a syntactical check on JML parse trees.
 *
 * @author Alexander Weigl
 * @version 1 (6/8/21)
 */
public interface JmlCheck {
    /**
     * Checks for the given parse tree and returns warnings if necessary.
     *
     * @param ctx an arbitrary {@link ParserRuleContext} from the {@link JmlParser}
     * @return a potential empty list of warnings
     */
    @Nonnull
    List<PositionedString> check(@Nonnull ParserRuleContext ctx);
}
