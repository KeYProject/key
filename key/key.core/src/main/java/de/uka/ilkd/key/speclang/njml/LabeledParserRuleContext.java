package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import org.antlr.v4.runtime.ParserRuleContext;

import javax.annotation.Nonnull;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
public class LabeledParserRuleContext {
    @Nonnull
    public final ParserRuleContext first;

    @Nonnull
    public final List<TermLabel> second;

    public LabeledParserRuleContext(@Nonnull ParserRuleContext first, TermLabel second) {
        this.first = Objects.requireNonNull(first);
        if (second != null) {
            this.second = Collections.singletonList(second);
        } else {
            this.second = Collections.emptyList();
        }
    }

    public LabeledParserRuleContext(ParserRuleContext first) {
        this(first, (TermLabel) null);
    }

    public LabeledParserRuleContext(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        this(ctx, constructTermLabel(ctx, specType));
    }

    public LabeledParserRuleContext(@Nonnull ParserRuleContext first, List<TermLabel> second) {
        this.first = first;
        if (second != null) {
            this.second = Collections.unmodifiableList(second);
        } else {
            this.second = Collections.emptyList();
        }
    }

    private static TermLabel constructTermLabel(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        String filename = ctx.start.getTokenSource().getSourceName();
        int line = ctx.start.getLine();
        OriginTermLabel.Origin origin = new OriginTermLabel.FileOrigin(specType, filename, line);
        return new OriginTermLabel(origin);
    }
}
