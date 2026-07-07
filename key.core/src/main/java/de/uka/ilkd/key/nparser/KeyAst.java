/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser;

import java.io.PrintWriter;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.nparser.builder.BuilderHelpers;
import de.uka.ilkd.key.nparser.builder.ChoiceFinder;
import de.uka.ilkd.key.nparser.builder.FindProblemInformation;
import de.uka.ilkd.key.nparser.builder.IncludeFinder;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.scripts.ScriptBlock;
import de.uka.ilkd.key.scripts.ScriptCommandAst;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.JmlParserBaseVisitor;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.java.StringUtil;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

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

    public final @NonNull T ctx;

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
    public static class File extends KeyAst<JavaKeYParser.FileContext> {
        File(JavaKeYParser.FileContext ctx) {
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
                JavaKeYParser.ProofScriptEntryContext pctx = ctx.problem().proofScriptEntry();

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
        public Includes getIncludes(Path base) {
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
            JavaKeYParser.ProofContext a = ctx.proof();
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
         * See the grammar (JavaKeYParser.g4) for more possible elements.
         */
        public KeyAst.@Nullable Declarations getProblemHeader() {
            final JavaKeYParser.DeclsContext decls = ctx.decls();
            return new KeyAst.Declarations(decls);
        }
    }

    public static class ConfigurationFile extends KeyAst<JavaKeYParser.CfileContext> {
        ConfigurationFile(JavaKeYParser.CfileContext ctx) {
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

        public List<Configuration> asConfigurationList() {
            final var cfg = new ConfigurationBuilder();
            List<Object> res = cfg.visitCfile(ctx);
            if (!res.isEmpty())
                return (List<Configuration>) res.getFirst();
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

    public static class JMLProofScript extends KeyAst<JmlParser.AssertionProofContext> {

        private static class ObtainedVarsVisitor extends JmlParserBaseVisitor<Void> {
            private ImmutableList<LocationVariable> collectedVars = ImmutableList.of();
            private final JmlIO io;

            private ObtainedVarsVisitor(JmlIO io) {
                this.io = io;
            }

            @Override
            public Void visitProofCmd(JmlParser.ProofCmdContext ctx) {
                if (ctx.obtain != null) {
                    KeYJavaType type = io.translateType(ctx.typespec());
                    ProgramElementName name = new ProgramElementName(ctx.var.getText());
                    collectedVars =
                        collectedVars.prepend(new LocationVariable(name, new TypeRef(type), true));
                }
                return null;
            }
        }

        private static class TermCollectionVisitor extends JmlParserBaseVisitor<Void> {
            private ImmutableList<JmlParser.ExpressionContext> collectedTerms = ImmutableList.of();

            @Override
            public Void visitExpression(JmlParser.ExpressionContext ctx) {
                collectedTerms = collectedTerms.prepend(ctx);
                return null;
            }
        }

        private ImmutableList<LocationVariable> obtainedProgramVars;

        public JMLProofScript(JmlParser.@NonNull AssertionProofContext ctx) {
            super(ctx);
        }

        public static JMLProofScript fromContext(JmlParser.AssertionProofContext ctx) {
            if (ctx == null) {
                return null;
            } else {
                return new JMLProofScript(ctx);
            }
        }

        public ImmutableList<LocationVariable> getObtainedProgramVars(JmlIO io) {
            if (obtainedProgramVars == null) {
                var visitor = new ObtainedVarsVisitor(io);
                ctx.accept(visitor);
                obtainedProgramVars = visitor.collectedVars;
            }
            return obtainedProgramVars;
        }

        /**
         * returns a list of all term parse trees in this proof script.
         *
         * Todo: Consider caching the result if this is called very often.
         */
        public @NonNull ImmutableList<JmlParser.ExpressionContext> collectTerms() {
            TermCollectionVisitor visitor = new TermCollectionVisitor();
            ctx.accept(visitor);
            return visitor.collectedTerms.reverse();
        }
    }


    public static class Term extends KeyAst<JavaKeYParser.TermContext> {
        Term(JavaKeYParser.TermContext ctx) {
            super(ctx);
        }
    }

    public static class Seq extends KeyAst<JavaKeYParser.SeqContext> {
        Seq(JavaKeYParser.SeqContext ctx) {
            super(ctx);
        }
    }

    public static class Taclet extends KeyAst<JavaKeYParser.TacletContext> {
        public Taclet(JavaKeYParser.TacletContext taclet) {
            super(taclet);
        }
    }

    /**
     * This struct encapsulate the information of a proof script found in key files.
     *
     * @author Alexander Weigl
     * @version 1 (23.04.24)
     */
    public static class ProofScript extends KeyAst<JavaKeYParser.ProofScriptContext> {
        ProofScript(JavaKeYParser.@NonNull ProofScriptContext ctx) {
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
                List<JavaKeYParser.ProofScriptCommandContext> cmds) {
            return cmds.stream().map(it -> asAst(file, it)).toList();
        }

        public static @NonNull ScriptBlock asAst(URI file,
                JavaKeYParser.ProofScriptCodeBlockContext ctx) {
            var loc = new Location(file, Position.fromToken(ctx.start));
            final var proofScriptCommandContexts = ctx.proofScript().proofScriptCommand();
            final List<ScriptCommandAst> list =
                proofScriptCommandContexts.stream()
                        .map(it -> asAst(file, it))
                        .toList();
            return new ScriptBlock(list, loc);
        }

        private static @NonNull ScriptCommandAst asAst(URI file,
                JavaKeYParser.ProofScriptCommandContext it) {
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

    /// Represents the user declarations in a KeY file.
    ///
    /// @author weigl
    public static class Declarations extends KeyAst<JavaKeYParser.DeclsContext> {
        protected Declarations(JavaKeYParser.DeclsContext ctx) {
            super(ctx);
        }

        public java.io.@Nullable File getJavaSourceLocation() {
            try {
                JavaKeYParser.String_valueContext value =
                    ctx.programSource(0).oneProgramSource().string_value(0);
                String v = ParsingFacade.getValueDocumentation(value);
                return new java.io.File(v);
            } catch (NullPointerException | IndexOutOfBoundsException e) {
                {
                    return null;
                }
            }
        }

        /// Prints the definitions, independent of paths, to the given {@link PrintWriter}.
        public void printDefinitions(PrintWriter out) {
            ctx.accept(new JavaKeYParserBaseVisitor<@Nullable Object>() {
                @Override
                public @Nullable Object visitOne_include(JavaKeYParser.One_includeContext ctx) {
                    if (ctx.absfile != null) {
                        out.printf("\\include %s;", ctx.absfile.getText());
                    }
                    return null;
                }

                @Override
                public @Nullable Object visitOptions_choice(
                        JavaKeYParser.Options_choiceContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitOption_decls(JavaKeYParser.Option_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitSort_decls(JavaKeYParser.Sort_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitProg_var_decls(
                        JavaKeYParser.Prog_var_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitSchema_var_decls(
                        JavaKeYParser.Schema_var_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitPred_decls(JavaKeYParser.Pred_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitFunc_decls(JavaKeYParser.Func_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitTransform_decls(
                        JavaKeYParser.Transform_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitDatatype_decls(
                        JavaKeYParser.Datatype_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }


                @Override
                public @Nullable Object visitRuleset_decls(JavaKeYParser.Ruleset_declsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }


                @Override
                public @Nullable Object visitContracts(JavaKeYParser.ContractsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitInvariants(JavaKeYParser.InvariantsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                @Override
                public @Nullable Object visitRulesOrAxioms(JavaKeYParser.RulesOrAxiomsContext ctx) {
                    printAsIs(ctx);
                    return null;
                }

                private void printAsIs(ParserRuleContext ctx) {
                    if (ctx != null) {
                        final Token start = ctx.start;
                        final Token stop = ctx.stop;
                        if (start != null && stop != null) {
                            int a = start.getStartIndex();
                            int b = stop.getStopIndex();
                            Interval interval = new Interval(a, b);
                            CharStream input = ctx.start.getInputStream();
                            out.println(input.getText(interval));
                        }
                    }
                }
            });


        }
    }
}
