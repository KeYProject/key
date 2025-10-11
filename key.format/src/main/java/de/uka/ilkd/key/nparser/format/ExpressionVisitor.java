/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.Set;

/**
 * Visitor class for formatting expressions in the KeY language.
 * <p>
 * This class extends the `KeYParserBaseVisitor` and provides custom
 * implementations for visiting terminal nodes and if-then-else terms.
 * It uses an `Output` object to format and output the tokens.
 * <p>
 * The class handles specific formatting rules for operators, braces,
 * and modalities, ensuring proper indentation and spacing.
 *
 * @author Julian Wiesler
 * @see Output
 */
class ExpressionVisitor extends KeYParserBaseVisitor<Void> {
    private static final Set<Integer> OPERATORS = Set.of(
            KeYLexer.LESS,
            KeYLexer.LESSEQUAL,
            KeYLexer.GREATER,
            KeYLexer.GREATEREQUAL,
            KeYLexer.EQUALS,
            KeYLexer.IMP,
            KeYLexer.SEQARROW,
            KeYLexer.NOT_EQUALS,
            KeYLexer.AND,
            KeYLexer.OR,
            KeYLexer.PARALLEL,
            KeYLexer.EXP,
            KeYLexer.PERCENT,
            KeYLexer.STAR,
            KeYLexer.MINUS,
            KeYLexer.PLUS,
            KeYLexer.EQV,
            KeYLexer.ASSIGN);

    private static final Set<Integer> BRACES = Set.of(
            KeYLexer.LBRACE, KeYLexer.LPAREN, KeYLexer.LBRACKET, KeYLexer.LGUILLEMETS);

    private final CommonTokenStream ts;
    private final Output output;

    public ExpressionVisitor(CommonTokenStream ts, Output output) {
        this.ts = ts;
        this.output = output;
    }

    private static void outputModality(Token token, String text, Output output) {
        var normalized = text.replaceAll("\t", Output.getIndent(1));
        var lines = normalized.split("\n");
        lines[0] = lines[0].trim();

        // Find the smallest indent of all lines except the first
        int minIndent = Integer.MAX_VALUE;
        for (int i = 1; i < lines.length; i++) {
            var line = lines[i];
            lines[i] = line.stripTrailing();
            var indent = line.length() - line.stripLeading().length();
            minIndent = Math.min(minIndent, indent);
        }

        output.token(lines[0]);
        if (lines.length > 1) {
            output.enterIndent(token);

            for (int i = 1; i < lines.length; i++) {
                output.newLine();
                var line = lines[i];
                if (!line.isEmpty()) {
                    output.token(line.substring(minIndent));
                }
            }
            output.exitIndent(token);
        }
        output.spaceBeforeNext();
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        var stream = ts;
        final var token = node.getSymbol();
        var pos = token.getTokenIndex();
        var nextType = pos + 1 < stream.size() ? stream.get(pos + 1).getType() : -1;

        int type = token.getType();

        if (type == KeYLexer.COLON) {
            output.noSpaceBeforeNext();
        }

        boolean isLBrace = BRACES.contains(type);
        if (type == KeYLexer.RBRACE || type == KeYLexer.RPAREN || type == KeYLexer.RBRACKET
                || type == KeYLexer.RGUILLEMETS) {
            output.noSpaceBeforeNext();
            output.exitIndent(token);
        }

        var isOperator = OPERATORS.contains(type);
        var isUnaryMinus = type == KeYLexer.MINUS &&
                node.getParent() instanceof KeYParser.Unary_minus_termContext;
        // Unary minus has a "soft" leading space, we allow it if the type before wants it but
        // don't require it
        if ((isOperator && !isUnaryMinus) || type == KeYLexer.AVOID) {
            output.spaceBeforeNext();
        }

        String text = token.getText();
        if (type == KeYLexer.MODALITY) {
            outputModality(token, text, output);
        } else {
            output.token(text);
        }

        if (!isLBrace && ((isOperator && !isUnaryMinus) ||
                type == KeYLexer.COMMA ||
                type == KeYLexer.SUBST ||
                type == KeYLexer.AVOID ||
                type == KeYLexer.EXISTS ||
                type == KeYLexer.FORALL ||
                type == KeYLexer.SEMI)
                || type == KeYLexer.IFEX
                || (type == KeYLexer.IDENT && nextType == KeYLexer.IDENT)) {
            output.spaceBeforeNext();
        }

        if (isLBrace) {
            output.enterIndent(token);
        }

        KeyFileFormatter.processHiddenTokensAfterCurrent(token, ts, output);
        return super.visitTerminal(node);
    }

    @Override
    public Void visitIfThenElseTerm(KeYParser.IfThenElseTermContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                final var token = ((TerminalNode) child).getSymbol();
                var type = token.getType();
                if (type == KeYParser.THEN) {
                    output.enterIndent(token);
                }

                if (type == KeYParser.THEN || type == KeYParser.ELSE) {
                    output.spaceBeforeNext();
                }
            }
            visit(child);
        }
        output.exitIndent(ctx.stop);
        return null;
    }
}
