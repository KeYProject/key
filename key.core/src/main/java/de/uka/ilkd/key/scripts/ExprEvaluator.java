/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeYParser.*;
import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;

import org.key_project.prover.sequent.Sequent;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.key_project.util.java.StringUtil.trim;

/// Evaluates expression inside of proof script to their appropriate type.
///
/// - [JmlParser.ExpressionContext]: [Term]
/// - [SeqContext]: [Sequent]
/// - [Boolean_literalContext]: [Boolean]
/// - [IntegerContext]: [Integer]
/// - [DoubleLiteralContext]: [Double]
/// - [String_literalContext]: [String]
///
/// @author Alexander Weigl
/// @version 1 (18.01.25)
/// @see de.uka.ilkd.key.nparser.KeYParser.ProofScriptExpressionContext
class ExprEvaluator extends KeYParserBaseVisitor<Object> {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExprEvaluator.class);
    private final EngineState state;

    ExprEvaluator(EngineState engineState) {
        this.state = engineState;
    }

    @Override
    public @NonNull Object visitBoolean_literal(@NonNull Boolean_literalContext ctx) {
        return Boolean.parseBoolean(ctx.getText());
    }

    @Override
    public @NonNull Object visitChar_literal(KeYParser.@NonNull Char_literalContext ctx) {
        return ctx.getText().charAt(1); // skip "'"
    }

    @Override
    public @NonNull Object visitInteger(@NonNull IntegerContext ctx) {
        return Integer.parseInt(ctx.getText());
    }

    @Override
    public @NonNull Object visitFloatLiteral(KeYParser.@NonNull FloatLiteralContext ctx) {
        return Float.parseFloat(ctx.getText());
    }

    @Override
    public @NonNull Object visitDoubleLiteral(@NonNull DoubleLiteralContext ctx) {
        return Double.parseDouble(ctx.getText());
    }

    @Override
    public @NonNull String visitString_literal(@NonNull String_literalContext ctx) {
        return trim(ctx.getText(), '"');
    }

    @Override
    public @NonNull Sequent visitSeq(@NonNull SeqContext ctx) {
        var expressionBuilder =
            new ExpressionBuilder(state.getProof().getServices(), state.getCurrentNamespaces());
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        var t = (Sequent) ctx.accept(expressionBuilder);
        var warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return t;

    }

    @Override
    public @NonNull Object visitSimple_ident(Simple_identContext ctx) {
        return evaluateExpression(ctx);
    }

    @Override
    public @NonNull Object visitTerm(KeYParser.TermContext ctx) {
        return evaluateExpression(ctx);
    }

    private @NonNull Object evaluateExpression(@NonNull ParserRuleContext ctx) {
        var expressionBuilder =
            new ExpressionBuilder(state.getProof().getServices(), state.getCurrentNamespaces());
        expressionBuilder.setAbbrevMap(state.getAbbreviations());
        var t = ctx.accept(expressionBuilder);
        var warnings = expressionBuilder.getBuildingIssues();
        warnings.forEach(it -> LOGGER.warn("{}", it));
        warnings.clear();
        return t;
    }

    @Override
    protected Object aggregateResult(Object aggregate, @Nullable Object nextResult) {
        return nextResult == null ? aggregate : nextResult;
    }
}
