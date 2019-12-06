package de.uka.ilkd.key.nparser;

import com.google.common.base.CharMatcher;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.Triple;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.jetbrains.annotations.NotNull;

import java.net.URL;

/**
 * This is a monad around the parse tree.
 * We use this class to hide the {@link org.antlr.v4.runtime.ParserRuleContext}
 * from the rest of the Key system.
 *
 * <p>
 * To obtain an KeYAst use the {@link ParsingFacade}.
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (5.12.19)
 */
public abstract class KeyAst<T extends ParserRuleContext> {
    @NotNull
    final T ctx;

    protected KeyAst(@NotNull T ctx) {
        this.ctx = ctx;
    }

    public <T> T accept(ParseTreeVisitor<T> visitor) {
        return ctx.accept(visitor);
    }

    public static class File extends KeyAst<KeYParser.FileContext> {
        File(KeYParser.FileContext ctx) {
            super(ctx);
        }

        public ProofSettings findProofSettings() {
            ProofSettingsFinder psf = new ProofSettingsFinder();
            ctx.accept(psf);
            return psf.getProofSettings();
        }

        public Triple<String, Integer, Integer> findProofScript() {
            if (ctx.problem() != null && ctx.problem().proofScript() != null) {
                var pctx = ctx.problem().proofScript();
                var text = pctx.ps.getText();
                return new Triple<>(CharMatcher.is('"').trimFrom(text), pctx.ps.getLine(), pctx.ps.getCharPositionInLine());
            }
            return null;
        }

        public Includes getIncludes(URL base) {
            var finder = new IncludeFinder(base);
            accept(finder);
            return finder.getIncludes();
        }

        public ChoiceInformation getChoices() {
            var finder = new ChoiceFinder();
            accept(finder);
            return finder.getChoiceInformation();
        }

        public ProblemInformation getProblemInformation() {
            FindProblemInformation fpi = new FindProblemInformation();
            ctx.accept(fpi);
            return fpi.getProblemInformation();
        }

        public Token findProof() {
            var a = ctx.proof();
            if (a != null)
                return a.PROOF().getSymbol();
            return null;
        }

        /**
         * Extracts the decls and taclets into a string.
         * This method is required for saving and loading proofs.
         * 
         * @return
         */
        public String getProblemHeader() {
            return ctx.decls().getText();
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
}
