/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.nparser.builder.FindProblemInformation;
import de.uka.ilkd.key.nparser.builder.IncludeFinder;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.scripts.ScriptBlock;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.java.StringUtil;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * This is a monad around the parse tree. We use this class to hide the
 * {@link ParserRuleContext} from the rest of the Key system.
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

    /// Apply the given `visitor` to the underlying ANTLR4 parse tree.
    public <R> R accept(ParseTreeVisitor<R> visitor) {
        return ctx.accept(visitor);
    }

    @Override
    public String toString() {
        return getClass().getName() + ": " + BuilderHelpers.getPosition(ctx);
    }

    /// Returns the start location of the first character of the first token of the underlying parse
    /// tree.
    public Location getStartLocation() {
        return Location.fromToken(ctx.start);
    }

    /// Get the text of the parse tree as a cut out of the original input stream.
    /// Hence, Spaces and comments should be preserved.
    public String getText() {
        var interval = new Interval(ctx.start.getStartIndex(), ctx.stop.getStopIndex() + 1);
        return ctx.start.getInputStream().getText(interval);
    }

    /// An AST representing a complete KeY file.
    public static class File extends KeyAst<KeYParser.FileContext> {
        File(KeYParser.FileContext ctx) {
            super(ctx);
        }

        /// Returns proof settings (aka `\settings`) if found in the parse tree.
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

        /**
         * Returns the a {@link ProofScriptEntry} from the underlying AST if an {@code \proofscript}
         * entry is present.
         * The {@code url} is used as the source of input and might be later used for error message,
         * or including
         * other files.
         *
         * @return a {@link ProofScriptEntry} if {@code \proofscript} is present
         */
        public @Nullable ProofScript findProofScript() {
            if (ctx.problem() != null && ctx.problem().proofScriptEntry() != null) {
                KeYParser.ProofScriptEntryContext pctx = ctx.problem().proofScriptEntry();

                if (pctx.STRING_LITERAL() != null) {
                    var ctx = pctx.STRING_LITERAL().getSymbol();
                    String text = pctx.STRING_LITERAL().getText();

                    // +1 for the removal of the quote.
                    text = StringUtil.move(StringUtil.trim(text, '"'), ctx.getLine(),
                        ctx.getCharPositionInLine() + 1);
                    return ParsingFacade.parseScript(
                        CharStreams.fromString(text, ctx.getTokenSource().getSourceName()));
                } else {
                    return new KeyAst.ProofScript(pctx.proofScript());
                }
            }
            return null;
        }

        /// Returns the includes (possible empty but not null) computed from the underlying parse
        /// tree.
        public Includes getIncludes(URL base) {
            IncludeFinder finder = new IncludeFinder(base);
            accept(finder);
            return finder.getIncludes();
        }

        /// Returns the information on choices from the underlying parse tree.
        public ChoiceInformation getChoices() {
            ChoiceFinder finder = new ChoiceFinder();
            accept(finder);
            return finder.getChoiceInformation();
        }

        /// Returns information on `\problem`, `\proofObligation` or `\chooseContract` using the
        /// underlying
        /// parse tree.
        public ProblemInformation getProblemInformation() {
            FindProblemInformation fpi = new FindProblemInformation();
            ctx.accept(fpi);
            return fpi.getProblemInformation();
        }

        /// Returns the token `\proof` in the underlying parse tree.`
        /// This token also marks the end of the parse tree (EOF) but not the end of the file.
        /// Positional information of the token is used to set up the proof replayer.
        public @Nullable Token findProof() {
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
                return (Configuration) res.getFirst();
            else
                throw new RuntimeException("Error in configuration. Source: "
                    + ctx.start.getTokenSource().getSourceName());
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

    /**
     * This struct encapsulate the information of a proof script found in key files.
     *
     * @author Alexander Weigl
     * @version 1 (23.04.24)
     */
    public static class ProofScript extends KeyAst<KeYParser.ProofScriptContext> {
        ProofScript(KeYParser.@NonNull ProofScriptContext ctx) {
            super(ctx);
        }

        public URI getUri() {
            return getUri(ctx.start);
        }

        public static URI getUri(Token token) {
            final var sourceName = token.getTokenSource().getSourceName();
            try {
                if (sourceName.startsWith("file:") || sourceName.startsWith("http:")
                        || sourceName.startsWith("jar:"))
                    return new URI(sourceName);
            } catch (URISyntaxException ignored) {
            }
            return new java.io.File(sourceName).toURI();
        }

        /// Translates this parse tree into an AST usable for the proof script engine.
        /// The current representation of a proof script is a list of commands. Each command
        /// can hold a list of sub-commands.
        ///
        /// @return a non-null list of the parsed commands.
        public List<ScriptCommandAst> asAst() {
            var fileUri = getUri();
            return asAst(fileUri, ctx.proofScriptCommand());
        }

        private static List<ScriptCommandAst> asAst(URI file,
                List<KeYParser.ProofScriptCommandContext> cmds) {
            return cmds.stream().map(it -> asAst(file, it)).toList();
        }

        public static @NonNull ScriptBlock asAst(URI file,
                KeYParser.ProofScriptCodeBlockContext ctx) {
            var loc = new Location(file, Position.fromToken(ctx.start));
            final var proofScriptCommandContexts = ctx.proofScript().proofScriptCommand();
            final List<ScriptCommandAst> list =
                proofScriptCommandContexts.stream()
                        .map(it -> asAst(file, it))
                        .toList();
            return new ScriptBlock(list, loc);
        }

        private static @NonNull ScriptCommandAst asAst(URI file,
                KeYParser.ProofScriptCommandContext it) {
            var loc = new Location(file, Position.fromToken(it.start));
            var nargs = new HashMap<String, Object>();
            var pargs = new ArrayList<>();

            if (it.proofScriptParameters() != null) {
                for (var param : it.proofScriptParameters().proofScriptParameter()) {
                    var expr = param.expr;
                    Object value = expr;
                    if (expr.proofScriptCodeBlock() != null) {
                        value = asAst(file, expr.proofScriptCodeBlock());
                    }

                    if (param.pname != null) {
                        nargs.put(param.pname.getText(), value);
                    } else {
                        pargs.add(value);
                    }
                }
            }

            return new ScriptCommandAst(it.cmd.getText(), nargs, pargs, loc);
        }
    }
}
