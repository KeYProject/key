package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.nparser.builder.FindProblemInformation;
import de.uka.ilkd.key.nparser.builder.IncludeFinder;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.PositionedString;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;

/**
 * This is a monad around the parse tree. We use this class to hide the
 * {@link org.antlr.v4.runtime.ParserRuleContext} from the rest of the Key system.
 *
 * <p>
 * To obtain an KeYAst use the {@link ParsingFacade#getParseRuleContext(KeyAst)}.
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (5.12.19)
 */
public abstract class KeyAst<T extends ParserRuleContext> {
    @Nonnull
    final T ctx;

    protected KeyAst(@Nonnull T ctx) {
        this.ctx = ctx;
    }

    public <T> T accept(ParseTreeVisitor<T> visitor) {
        return ctx.accept(visitor);
    }

    @Override
    public String toString() {
        return getClass().getName() + ": " + BuilderHelpers.getPosition(ctx);
    }

    public static class File extends KeyAst<KeYParser.FileContext> {
        File(KeYParser.FileContext ctx) {
            super(ctx);
        }

        @Nullable
        public ProofSettings findProofSettings() {
            ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);
            if (ctx.decls() != null && ctx.decls().pref != null) {
                String text =
                    StringUtil.trim(ctx.decls().pref.s.getText(), '"').replace("\\\\:", ":");
                settings.loadSettingsFromString(text);
            }
            return settings;
        }

        @Nullable
        public ProofScript findProofScript() {
            if (ctx.problem() != null && ctx.problem().proofScriptEntry() != null) {
                var pctx = ctx.problem().proofScriptEntry();
                if (pctx.STRING_LITERAL() != null) {
                    var ps = new PositionedString(pctx.STRING_LITERAL().getText(), pctx.STRING_LITERAL().getSymbol());
                    return ParsingFacade.parseScript(ps);
                } else {
                    return new KeyAst.ProofScript(pctx.proofScript());
                }
            }
            return null;
        }

        public Includes getIncludes(URL base) {
            IncludeFinder finder = new IncludeFinder(base);
            accept(finder);
            return finder.getIncludes();
        }

        public ChoiceInformation getChoices() {
            ChoiceFinder finder = new ChoiceFinder();
            accept(finder);
            return finder.getChoiceInformation();
        }

        public ProblemInformation getProblemInformation() {
            FindProblemInformation fpi = new FindProblemInformation();
            ctx.accept(fpi);
            return fpi.getProblemInformation();
        }

        public Token findProof() {
            KeYParser.ProofContext a = ctx.proof();
            if (a != null)
                return a.PROOF().getSymbol();
            return null;
        }

        /**
         * Extracts the decls and taclets into a string. This method is required for saving and
         * loading proofs.
         */
        public String getProblemHeader() {
            final KeYParser.DeclsContext decls = ctx.decls();
            if (decls != null) {
                final Token start = decls.start;
                final Token stop = decls.stop;
                if (start != null && stop != null) {
                    int a = start.getStartIndex();
                    int b = stop.getStopIndex();
                    Interval interval = new Interval(a, b);
                    CharStream input = ctx.start.getInputStream();
                    return input.getText(interval);
                }
            }
            return "";
        }
    }

    public static class Term extends KeyAst<KeYParser.TermContext> {
        Term(KeYParser.TermContext ctx) {
            super(ctx);
        }
    }

    public static class Seq extends KeyAst<KeYParser.SeqContext> {
        Seq(KeYParser.SeqContext ctx) {
            super(ctx);
        }
    }

    public static class ProofScript extends KeyAst<KeYParser.ProofScriptContext> {
        ProofScript(@Nonnull KeYParser.ProofScriptContext ctx) {
            super(ctx);
        }

        public URL getUrl() {
            try {
                final var sourceName = ctx.start.getTokenSource().getSourceName();
                if(sourceName.startsWith("file:") || sourceName.startsWith("http:") || sourceName.startsWith("jar:"))
                    return new URL(sourceName);
                else
                    return new java.io.File(sourceName).toURI().toURL();
            } catch (MalformedURLException e) {
                e.printStackTrace();
                return null;
            }
        }
    }
}
