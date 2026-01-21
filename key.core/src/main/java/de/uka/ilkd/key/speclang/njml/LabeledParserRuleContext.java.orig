package de.uka.ilkd.key.speclang.njml;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.origin.TermOrigin;
import org.antlr.v4.runtime.ParserRuleContext;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.net.URI;

/**
 * This class maps a {@link ParserRuleContext} to a {@link TermLabel}.
 */
public class LabeledParserRuleContext {
    @Nonnull
    public final ParserRuleContext first;
    @Nullable
    public final TermLabel second;
    @Nullable
    public final TermOrigin origin;

    public LabeledParserRuleContext(ParserRuleContext first, TermLabel second) {
        if (first == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = first;
        this.second = second;
        this.origin = null;
    }


    public LabeledParserRuleContext(ParserRuleContext first) {
        if (first == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = first;
        this.second = null;
        this.origin = null;
    }

    public LabeledParserRuleContext(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        if (ctx == null) throw new IllegalArgumentException("ParserRuleContext is null");
        this.first = ctx;
        this.second = constructTermLabel(ctx, specType);
        this.origin = constructOrigin(ctx, specType);
    }

    private static TermLabel constructTermLabel(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {
        String filename = ctx.start.getTokenSource().getSourceName();
        int line = ctx.start.getLine();
        OriginTermLabel.Origin origin = new OriginTermLabel.FileOrigin(specType, filename, line);
        return new OriginTermLabel(origin);
    }

    private static TermOrigin constructOrigin(ParserRuleContext ctx, OriginTermLabel.SpecType specType) {

        String src = ctx.start.getTokenSource().getSourceName();

        return new TermOrigin(src, ctx.start.getLine(), ctx.stop.getLine(), ctx.start.getTokenIndex(), ctx.stop.getTokenIndex(), specType);
    }

    public Term addOrigin(TermBuilder tb, Term term) {
        if (origin == null) return term;

        ImmutableArray<TermOrigin> arr = new ImmutableArray<>(origin);

        return tb.tf().createTerm(term.op(), term.subs(), term.boundVars(), term.javaBlock(), term.getLabels(), arr);
    }
}
