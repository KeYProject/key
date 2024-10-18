/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.format;

import de.uka.ilkd.key.nparser.KeYLexer;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.Set;

/**
 * @author Julian Wiesler
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

    private static void outputModality(String text, Output output) {
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
            output.enterIndent();

            for (int i = 1; i < lines.length; i++) {
                output.newLine();
                var line = lines[i];
                if (!line.isEmpty()) {
                    output.token(line.substring(minIndent));
                }
            }
            output.exitIndent();
        }
        output.spaceBeforeNext();
    }

    @Override
    public Void visitTerminal(TerminalNode node) {
        int token = node.getSymbol().getType();

        boolean isLBrace = BRACES.contains(token);
        if (token == KeYLexer.RBRACE || token == KeYLexer.RPAREN || token == KeYLexer.RBRACKET
                || token == KeYLexer.RGUILLEMETS) {
            output.noSpaceBeforeNext();
            output.exitIndent();
        }

        var isOperator = OPERATORS.contains(token);
        var isUnaryMinus = token == KeYLexer.MINUS &&
                node.getParent() instanceof KeYParser.Unary_minus_termContext;
        // Unary minus has a "soft" leading space, we allow it if the token before wants it but
        // don't require it
        if ((isOperator && !isUnaryMinus) || token == KeYLexer.AVOID) {
            output.spaceBeforeNext();
        }

        String text = node.getSymbol().getText();
        if (token == KeYLexer.MODALITY) {
            outputModality(text, output);
        } else {
            output.token(text);
        }

        if (!isLBrace && ((isOperator && !isUnaryMinus) ||
                token == KeYLexer.COMMA ||
                token == KeYLexer.SUBST ||
                token == KeYLexer.AVOID ||
                token == KeYLexer.EXISTS ||
                token == KeYLexer.FORALL ||
                token == KeYLexer.SEMI)) {
            output.spaceBeforeNext();
        }

        if (isLBrace) {
            output.enterIndent();
        }

        KeYFileFormatter.processHiddenTokensAfterCurrent(node.getSymbol(), ts, output);
        return super.visitTerminal(node);
    }

    @Override
    public Void visitIfThenElseTerm(KeYParser.IfThenElseTermContext ctx) {
        for (int i = 0; i < ctx.getChildCount(); i++) {
            var child = ctx.getChild(i);
            if (child instanceof TerminalNode) {
                var token = ((TerminalNode) child).getSymbol().getType();
                if (token == KeYParser.THEN) {
                    output.enterIndent();
                }

                if (token == KeYParser.THEN || token == KeYParser.ELSE) {
                    output.spaceBeforeNext();
                }
            }
            visit(child);
        }
        output.exitIndent();
        return null;
    }
}
