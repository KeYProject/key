/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.net.URL;
import java.util.List;

import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.nparser.builder.FindProblemInformation;
import de.uka.ilkd.key.nparser.builder.IncludeFinder;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.util.Triple;

import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

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

    final @NonNull T ctx;

    protected KeyAst(@NonNull T ctx) {
        this.ctx = ctx;
    }

    public <T> T accept(ParseTreeVisitor<T> visitor) {
        return ctx.accept(visitor);
    }

    @Override
    public String toString() {
        return getClass().getName() + ": " + BuilderHelpers.getPosition(ctx);
    }

    public Location getStartLocation() {
        return Location.fromToken(ctx.start);
    }

    public String getText() {
        var interval = new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex() + 1);
        return ctx.start.getInputStream().getText(interval);
    }

    public static class File extends KeyAst<KeYParser.FileContext> {
        File(KeYParser.FileContext ctx) {
            super(ctx);
        }

        public @Nullable ProofSettings findProofSettings() {
            ProofSettings settings = new ProofSettings(ProofSettings.DEFAULT_SETTINGS);

            if (ctx.preferences() != null && ctx.preferences().s != null) {
                String text = StringUtil.trim(ctx.preferences().s.getText(), '"')
                        .replace("\\\\:", ":");
                settings.loadSettingsFromPropertyString(text);
            } else if (ctx.preferences() != null && ctx.preferences().c != null) {
                var cb = new ConfigurationBuilder();
                var c = (Configuration) ctx.preferences().c.accept(cb);
                settings.readSettings(c);
            }
            return settings;
        }

        public @Nullable Triple<String, Integer, Integer> findProofScript() {
            if (ctx.problem() != null && ctx.problem().proofScript() != null) {
                KeYParser.ProofScriptContext pctx = ctx.problem().proofScript();
                String text = pctx.ps.getText();
                return new Triple<>(StringUtil.trim(text, '"'), pctx.ps.getLine(),
                    pctx.ps.getCharPositionInLine());
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
            if (a != null) {
                return a.PROOF().getSymbol();
            }
            return null;
        }

        /**
         * Extracts the decls and taclets into a string.
         * The problem header may contain the bootstrap classpath,
         * the regular classpath, the Java source file to load,
         * include statements to load other files, configuration of options,
         * declarations of sorts, program variables, schema variables, predicates, and more.
         * See the grammar (KeYParser.g4) for more possible elements.
         */
        public String getProblemHeader() {
            final KeYParser.DeclsContext decls = ctx.decls();
            if (decls != null && decls.getChildCount() > 0) {
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

    public static class ConfigurationFile extends KeyAst<KeYParser.CfileContext> {
        ConfigurationFile(KeYParser.CfileContext ctx) {
            super(ctx);
        }

        public Configuration asConfiguration() {
            final var cfg = new ConfigurationBuilder();
            List<Object> res = cfg.visitCfile(ctx);
            if (!res.isEmpty())
                return (Configuration) res.get(0);
            else
                throw new RuntimeException();
        }
    }

    public static class SetStatementContext extends KeyAst<JmlParser.Set_statementContext> {
        public SetStatementContext(JmlParser.@NonNull Set_statementContext ctx) {
            super(ctx);
        }

        public Expression getAssignee() {
            return new Expression(ctx.assignee);
        }

        public Expression getValue() {
            return new Expression(ctx.value);
        }
    }

    public static class Expression extends KeyAst<JmlParser.ExpressionContext> {
        public Expression(JmlParser.@NonNull ExpressionContext ctx) {
            super(ctx);
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

    public static class Taclet extends KeyAst<KeYParser.TacletContext> {
        public Taclet(KeYParser.TacletContext taclet) {
            super(taclet);
        }
    }
}
