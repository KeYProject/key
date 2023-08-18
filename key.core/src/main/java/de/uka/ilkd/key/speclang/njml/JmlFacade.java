/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.net.URI;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * This facade provides facilities for the creation of lexer and parser of JML. It is the
 * programatically frontend for the {@code JMLLexer.g4} and {@code JMLParser.g4}. This class is
 * rather a thin layer upon ANTLR4.
 * <p>
 * As a normal KeY developer you should rather {@link JmlIO}. {@link JmlIO} provides a translation
 * from strings into KeY constructs.
 *
 * @author Alexander Weigl
 * @version 1 (5/10/20)
 * @see JmlIO
 */
public final class JmlFacade {

    private JmlFacade() {
    }

    /**
     * Creates an JML lexer for the give stream.
     */
    public static @Nonnull JmlLexer createLexer(@Nonnull CharStream stream) {
        return new JmlLexer(stream);
    }

    /**
     * Creates a JML lexer for the given string with position. The position information of the lexer
     * is changed accordingly.
     */
    public static @Nonnull JmlLexer createLexer(@Nonnull PositionedString ps) {
        CharStream result = CharStreams.fromString(ps.text,
            ps.getLocation().getFileURI().map(URI::toString).orElse(null));
        JmlLexer lexer = createLexer(result);
        Position pos = ps.getLocation().getPosition();
        if (!pos.isNegative()) {
            lexer.getInterpreter().setCharPositionInLine(pos.column() - 1);
            lexer.getInterpreter().setLine(pos.line());
        }
        return lexer;
    }

    /**
     * Creates a JML lexer for a given string.
     */
    public static @Nonnull JmlLexer createLexer(@Nonnull String content) {
        return createLexer(CharStreams.fromString(content));
    }

    /**
     * Parse the given string as an JML expr. Position information are updated accordingly to the
     * position given with the string.
     */
    public static @Nonnull ParserRuleContext parseExpr(@Nonnull PositionedString expr) {
        return getExpressionContext(createLexer(expr));
    }

    /**
     * Parse the given string as an JML expr.
     */
    public static ParserRuleContext parseExpr(String expr) {
        return getExpressionContext(createLexer(expr));
    }

    private static ParserRuleContext getExpressionContext(JmlLexer lexer) {
        lexer._mode = JmlLexer.expr;
        JmlParser parser = createParser(lexer);
        JmlParser.ExpressionEOFContext ctx = parser.expressionEOF();
        ParserRuleContext c;
        if (ctx.expression() != null) {
            c = ctx.expression();
        } else {
            c = ctx.storeref();
        }
        if (c == null) {
            throw new NullPointerException();
        }
        return c;
    }

    /**
     * Create a JML parser for a given lexer. This method adds a exception-throwing error listeners
     * to the parser.
     *
     * @see SyntaxErrorReporter
     */
    public static @Nonnull JmlParser createParser(@Nonnull JmlLexer lexer) {
        JmlParser p = new JmlParser(new CommonTokenStream(lexer));
        p.addErrorListener(p.getErrorReporter());
        return p;
    }

    /**
     * Parses a given clause, like {@code ensures} or {@code requires} and returns a parse tree.
     */
    public static @Nonnull ParserRuleContext parseClause(@Nonnull String content) {
        JmlParser p = createParser(createLexer(content));
        JmlParser.ClauseContext ctx = p.clauseEOF().clause();
        p.getErrorReporter().throwException();
        return ctx;
    }
}
